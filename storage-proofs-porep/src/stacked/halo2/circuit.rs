use std::any::TypeId;
use std::convert::TryInto;
use std::marker::PhantomData;

use fil_halo2_gadgets::{
    boolean::AssignedBit,
    uint32::{self, AssignedU32, UInt32Chip, UInt32Config},
    sha256::{Sha256WordsChip, Sha256WordsConfig},
    AdviceIter, ColumnBuilder,
};
use filecoin_hashers::{
    poseidon::PoseidonHasher,
    sha256::Sha256Hasher,
    Domain, FieldArity, HaloHasher, HashInstructions, Hasher, PoseidonArity, POSEIDON_CONSTANTS,
};
use generic_array::typenum::U2;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance},
};
use storage_proofs_core::{
    gadgets::halo2::{
        insert::{InsertChip, InsertConfig},
        por::MerkleChip,
    },
};

use crate::stacked::{
    halo2::{
        constants::{
            challenge_count, num_layers, partition_count, DRG_PARENT_LABELS_WORD_LEN,
            EXP_PARENT_LABELS_WORD_LEN, LABEL_WORD_LEN, NUM_DRG_PARENTS, NUM_EXP_PARENTS,
            REPEATED_PARENT_LABELS_WORD_LEN,
        },
        gadgets::{
            ColumnHasherChip, ColumnHasherConfig, EncodingChip, EncodingConfig, LabelingChip,
            LabelingConfig,
        },
    },
};

trait CircuitParams<const SECTOR_NODES: usize> {
    const PARTITION_COUNT: usize = partition_count::<SECTOR_NODES>();
    const CHALLENGE_COUNT: usize = challenge_count::<SECTOR_NODES>();
    const NUM_LAYERS: usize = num_layers::<SECTOR_NODES>();
    // Absolute rows of public inputs.
    const REPLICA_ID_ROW: usize = 0;
    const COMM_D_ROW: usize = 1;
    const COMM_R_ROW: usize = 2;
    const FIRST_CHALLENGE_ROW: usize = 3;
    const CHALLENGE_ROWS: std::ops::Range<usize> = std::ops::Range {
        start: 3,
        end: 3 + Self::CHALLENGE_COUNT,
    };
}

#[derive(Clone)]
pub struct PublicInputs<F: FieldExt> {
    pub replica_id: Option<F>,
    pub comm_d: Option<F>,
    pub comm_r: Option<F>,
    pub challenges: Vec<Option<u32>>,
}

impl<F: FieldExt> PublicInputs<F> {
    pub fn to_vec(&self) -> Vec<Vec<F>> {
        assert!(
            self.replica_id.is_some()
                && self.comm_d.is_some()
                && self.comm_r.is_some()
                && self.challenges.iter().all(Option::is_some),
            "all public inputs must contain a value before converting into a vector",
        );

        let mut pub_inputs = Vec::with_capacity(self.challenges.len() + 3);
        pub_inputs.push(self.replica_id.unwrap());
        pub_inputs.push(self.comm_d.unwrap());
        pub_inputs.push(self.comm_r.unwrap());
        for c in &self.challenges {
            pub_inputs.push(F::from(c.unwrap() as u64));
        }

        vec![pub_inputs]
    }
}

fn empty_path_r<F, U, V, W, const SECTOR_NODES: usize>() -> Vec<Vec<Option<F>>>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    let base_arity = U::to_usize();
    let sub_arity = V::to_usize();
    let top_arity = W::to_usize();

    let challenge_bit_len = SECTOR_NODES.trailing_zeros() as usize;

    let base_height = {
        let mut base_challenge_bit_len = challenge_bit_len;
        if sub_arity != 0 {
            base_challenge_bit_len -= sub_arity.trailing_zeros() as usize;
        }
        if top_arity != 0 {
            base_challenge_bit_len -= top_arity.trailing_zeros() as usize;
        }
        base_challenge_bit_len / (base_arity.trailing_zeros() as usize)
    };

    let mut path_r = vec![vec![None; base_arity - 1]; base_height];
    if sub_arity != 0 {
        path_r.push(vec![None; sub_arity - 1]);
    }
    if top_arity != 0 {
        path_r.push(vec![None; top_arity - 1]);
    }

    path_r
}

#[derive(Clone)]
pub struct ParentProof<F, U, V, W, const SECTOR_NODES: usize>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    column: Vec<Option<F>>,
    path_c: Vec<Vec<Option<F>>>,
    _tree_r: PhantomData<(U, V, W)>,
}

impl<F, U, V, W, const SECTOR_NODES: usize> ParentProof<F, U, V, W, SECTOR_NODES>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    pub fn empty() -> Self {
        let num_layers = num_layers::<SECTOR_NODES>();
        ParentProof {
            column: vec![None; num_layers],
            path_c: empty_path_r::<F, U, V, W, SECTOR_NODES>(),
            _tree_r: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct ChallengeProof<F, U, V, W, const SECTOR_NODES: usize>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    leaf_d: Option<F>,
    path_d: Vec<Vec<Option<F>>>,
    path_c: Vec<Vec<Option<F>>>,
    path_r: Vec<Vec<Option<F>>>,
    drg_parent_proofs: [ParentProof<F, U, V, W, SECTOR_NODES>; NUM_DRG_PARENTS],
    exp_parent_proofs: [ParentProof<F, U, V, W, SECTOR_NODES>; NUM_EXP_PARENTS],
    _tree_r: PhantomData<(U, V, W)>,
}

impl<F, U, V, W, const SECTOR_NODES: usize> ChallengeProof<F, U, V, W, SECTOR_NODES>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    pub fn empty() -> Self {
        let challenge_bit_len = SECTOR_NODES.trailing_zeros() as usize;
        let path_d = vec![vec![None]; challenge_bit_len];
        let path_r = empty_path_r::<F, U, V, W, SECTOR_NODES>();

        ChallengeProof {
            leaf_d: None,
            path_d,
            path_c: path_r.clone(),
            path_r,
            drg_parent_proofs: [
                ParentProof::empty(), ParentProof::empty(), ParentProof::empty(),
                ParentProof::empty(), ParentProof::empty(), ParentProof::empty(),
            ],
            exp_parent_proofs: [
                ParentProof::empty(), ParentProof::empty(), ParentProof::empty(),
                ParentProof::empty(), ParentProof::empty(), ParentProof::empty(),
                ParentProof::empty(), ParentProof::empty(),
            ],
            _tree_r: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct PrivateInputs<F, U, V, W, const SECTOR_NODES: usize>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    pub comm_c: Option<F>,
    // `root_r` is `comm_r_last`.
    pub root_r: Option<F>,
    pub challenge_proofs: Vec<ChallengeProof<F, U, V, W, SECTOR_NODES>>,
}

#[derive(Clone)]
pub struct SdrPorepConfig<F, U, V, W, const SECTOR_NODES: usize>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    Sha256Hasher<F>: Hasher,
    <Sha256Hasher<F> as Hasher>::Domain: Domain<Field = F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    // Decomposes each challenge into 32 bits.
    uint32: UInt32Config<F>,
    // Converts a field element into eight `u32` words; each having SHA256's expected bit order.
    sha256_words: Sha256WordsConfig<F>,
    // Computes CommR.
    poseidon_2: <PoseidonHasher<F> as HaloHasher<U2>>::Config,
    // Hashes each column.
    column_hasher: ColumnHasherConfig<F, SECTOR_NODES>,
    // Computes root from TreeD Merkle proof.
    sha256: <Sha256Hasher<F> as HaloHasher<U2>>::Config,
    insert_2: InsertConfig<F, U2>,
    // Computes root from TreeR or TreeC Merkle proof.
    poseidon_base: <PoseidonHasher<F> as HaloHasher<U>>::Config,
    insert_base: InsertConfig<F, U>,
    sub: Option<(
        <PoseidonHasher<F> as HaloHasher<V>>::Config,
        InsertConfig<F, V>,
    )>,
    top: Option<(
        <PoseidonHasher<F> as HaloHasher<W>>::Config,
        InsertConfig<F, W>,
    )>,
    labeling: LabelingConfig<F, SECTOR_NODES>,
    encoding: EncodingConfig<F>,
    // Equality constrained advice.
    advice: Vec<Column<Advice>>,
    pi: Column<Instance>,
}

#[derive(Clone)]
pub struct SdrPorepCircuit<F, U, V, W, const SECTOR_NODES: usize>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    pub pub_inputs: PublicInputs<F>,
    pub priv_inputs: PrivateInputs<F, U, V, W, SECTOR_NODES>,
}

impl<F, U, V, W, const SECTOR_NODES: usize> CircuitParams<SECTOR_NODES> for
    SdrPorepCircuit<F, U, V, W, SECTOR_NODES>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
}

impl<F, U, V, W, const SECTOR_NODES: usize> Circuit<F> for SdrPorepCircuit<F, U, V, W, SECTOR_NODES>
where
    F: FieldExt,
    U: PoseidonArity<F>,
    V: PoseidonArity<F>,
    W: PoseidonArity<F>,
    Sha256Hasher<F>: Hasher,
    <Sha256Hasher<F> as Hasher>::Domain: Domain<Field = F>,
    PoseidonHasher<F>: Hasher,
    <PoseidonHasher<F> as Hasher>::Domain: Domain<Field = F>,
{
    type Config = SdrPorepConfig<F, U, V, W, SECTOR_NODES>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        SdrPorepCircuit {
            pub_inputs: PublicInputs {
                replica_id: None,
                comm_d: None,
                comm_r: None,
                challenges: vec![None; self.pub_inputs.challenges.len()],
            },
            priv_inputs: PrivateInputs {
                comm_c: None,
                root_r: None,
                challenge_proofs: vec![
                    ChallengeProof::empty();
                    self.priv_inputs.challenge_proofs.len()
                ],
            },
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let (advice_eq, advice_neq, fixed_eq, fixed_neq) = ColumnBuilder::new()
            .with_chip::<UInt32Chip<F>>()
            .with_chip::<Sha256WordsChip<F>>()
            .with_chip::<<PoseidonHasher<F> as HaloHasher<U2>>::Chip>()
            .with_chip::<ColumnHasherChip<F, SECTOR_NODES>>()
            // TreeD Merkle proof.
            .with_chip::<<Sha256Hasher<F> as HaloHasher<U2>>::Chip>()
            .with_chip::<InsertChip<F, U2>>()
            // TreeR/TreeC Merkle proof; only use the base arity because it is guaranteed to be the
            // largest TreeR arity, and thus, requires the greatest number of columns.
            .with_chip::<<PoseidonHasher<F> as HaloHasher<U>>::Chip>()
            .with_chip::<InsertChip<F, U>>()
            .create_columns(meta);

        let uint32 = UInt32Chip::configure(
            meta,
            advice_eq[..uint32::NUM_ADVICE_EQ].try_into().unwrap(),
        );

        let sha256_words = Sha256WordsChip::configure(
            meta,
            advice_eq[..uint32::NUM_ADVICE_EQ].try_into().unwrap(),
        );

        let poseidon_2 = <PoseidonHasher<F> as HaloHasher<U2>>::configure(
            meta,
            &advice_eq,
            &advice_neq,
            &fixed_eq,
            &fixed_neq,
        );

        let column_hasher = match Self::NUM_LAYERS {
            2 => ColumnHasherConfig::Arity2(poseidon_2.clone()),
            _ => ColumnHasherChip::configure(meta, &advice_eq, &advice_neq, &fixed_eq, &fixed_neq),
        };

        let sha256 = <Sha256Hasher<F> as HaloHasher<U2>>::configure(
            meta,
            &advice_eq,
            &advice_neq,
            &fixed_eq,
            &fixed_neq,
        );

        let insert_2 = InsertChip::configure(meta, &advice_eq, &advice_neq);

        let tree_d_arity_type = TypeId::of::<U2>();
        let base_arity_type = TypeId::of::<U>();
        let sub_arity_type = TypeId::of::<V>();
        let top_arity_type = TypeId::of::<W>();

        let (poseidon_base, insert_base) = if base_arity_type == tree_d_arity_type {
            // Convert each chip's `U2` type parameter to `U`.
            let poseidon_base = unsafe { std::mem::transmute(poseidon_2.clone()) };
            let insert_base = unsafe { std::mem::transmute(insert_2.clone()) };
            (poseidon_base, insert_base)
        } else {
            let poseidon_base = <PoseidonHasher<F> as HaloHasher<U>>::configure(
                meta,
                &advice_eq,
                &advice_neq,
                &fixed_eq,
                &fixed_neq,
            );
            let insert_base = InsertChip::<F, U>::configure(meta, &advice_eq, &advice_neq);
            (poseidon_base, insert_base)
        };

        let sub = if V::to_usize() == 0 {
            None
        } else if sub_arity_type == tree_d_arity_type {
            // Convert each chip's `U2` type parameter to `V`.
            let poseidon_sub = unsafe { std::mem::transmute(poseidon_2.clone()) };
            let insert_sub = unsafe { std::mem::transmute(insert_2.clone()) };
            Some((poseidon_sub, insert_sub))
        } else if sub_arity_type == base_arity_type {
            // Convert each chip's `U` type parameter to `V`.
            let poseidon_sub = unsafe { std::mem::transmute(poseidon_base.clone()) };
            let insert_sub = unsafe { std::mem::transmute(insert_base.clone()) };
            Some((poseidon_sub, insert_sub))
        } else {
            let poseidon_sub = <PoseidonHasher<F> as HaloHasher<V>>::configure(
                meta,
                &advice_eq,
                &advice_neq,
                &fixed_eq,
                &fixed_neq,
            );
            let insert_sub = InsertChip::<F, V>::configure(meta, &advice_eq, &advice_neq);
            Some((poseidon_sub, insert_sub))
        };

        let top = if W::to_usize() == 0 {
            None
        } else if top_arity_type == tree_d_arity_type {
            // Convert each chip's `U2` type parameter to `W`.
            let poseidon_top = unsafe { std::mem::transmute(poseidon_2.clone()) };
            let insert_top = unsafe { std::mem::transmute(insert_2.clone()) };
            Some((poseidon_top, insert_top))
        } else if top_arity_type == base_arity_type {
            // Convert each chip's `U` type parameter to `W`.
            let poseidon_top = unsafe { std::mem::transmute(poseidon_base.clone()) };
            let insert_top = unsafe { std::mem::transmute(insert_base.clone()) };
            Some((poseidon_top, insert_top))
        } else if top_arity_type == sub_arity_type {
            // Convert each chip's `V` type parameter to `W`.
            let (poseidon_sub, insert_sub) = sub.as_ref().unwrap();
            let poseidon_top = unsafe { std::mem::transmute(poseidon_sub.clone()) };
            let insert_top = unsafe { std::mem::transmute(insert_sub.clone()) };
            Some((poseidon_top, insert_top))
        } else {
            let poseidon_top = <PoseidonHasher<F> as HaloHasher<W>>::configure(
                meta,
                &advice_eq,
                &advice_neq,
                &fixed_eq,
                &fixed_neq,
            );
            let insert_top = InsertChip::<F, W>::configure(meta, &advice_eq, &advice_neq);
            Some((poseidon_top, insert_top))
        };

        let labeling = LabelingChip::configure(meta, sha256.clone(), &advice_eq);
        let encoding = EncodingChip::configure(meta, advice_eq[..3].try_into().unwrap());

        let pi = meta.instance_column();
        meta.enable_equality(pi);
        
        SdrPorepConfig {
            uint32,
            sha256_words,
            poseidon_2,
            column_hasher,
            sha256,
            insert_2,
            poseidon_base,
            insert_base,
            sub,
            top,
            labeling,
            encoding,
            advice: advice_eq,
            pi,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let SdrPorepCircuit {
            pub_inputs,
            priv_inputs,
            ..
        } = self;

        assert_eq!(pub_inputs.challenges.len(), Self::CHALLENGE_COUNT);
        assert_eq!(priv_inputs.challenge_proofs.len(), Self::CHALLENGE_COUNT);

        let SdrPorepConfig {
            uint32: uint32_config,
            sha256_words: sha256_words_config,
            poseidon_2: poseidon_2_config,
            column_hasher: column_hasher_config,
            sha256: sha256_config,
            insert_2: insert_2_config,
            poseidon_base: poseidon_base_config,
            insert_base: insert_base_config,
            sub: sub_config,
            top: top_config,
            labeling: labeling_config,
            encoding: encoding_config,
            advice,
            pi: pi_col,
        } = config;

        <Sha256Hasher<F> as HaloHasher<U2>>::load(&mut layouter, &sha256_config)?;

        let uint32_chip = UInt32Chip::construct(uint32_config);
        let sha256_words_chip = Sha256WordsChip::construct(sha256_words_config);
        let poseidon_2_chip = <PoseidonHasher<F> as HaloHasher<U2>>::construct(poseidon_2_config);
        let column_hasher_chip = ColumnHasherChip::construct(column_hasher_config);
        let labeling_chip = LabelingChip::construct(labeling_config);
        let encoding_chip = EncodingChip::construct(encoding_config);

        let tree_d_merkle_chip = {
            let sha256_chip = <Sha256Hasher<F> as HaloHasher<U2>>::construct(sha256_config);
            let insert_2_chip = InsertChip::construct(insert_2_config);
            MerkleChip::<Sha256Hasher<F>, U2>::with_subchips(sha256_chip, insert_2_chip, None, None)
        };

        let tree_r_merkle_chip = {
            let poseidon_base_chip = <PoseidonHasher<F> as HaloHasher<U>>::construct(poseidon_base_config);
            let insert_base_chip = InsertChip::construct(insert_base_config);
            let sub_chips = sub_config.map(|(poseidon_sub, insert_sub)| {
                (
                    <PoseidonHasher<F> as HaloHasher<V>>::construct(poseidon_sub),
                    InsertChip::construct(insert_sub),
                )
            });
            let top_chips = top_config.map(|(poseidon_top, insert_top)| {
                (
                    <PoseidonHasher<F> as HaloHasher<W>>::construct(poseidon_top),
                    InsertChip::construct(insert_top),
                )
            });
            MerkleChip::<PoseidonHasher<F>, U, V, W>::with_subchips(
                poseidon_base_chip,
                insert_base_chip,
                sub_chips,
                top_chips,
            )
        };

        // Decompose replica-id public input into 32-bit words.
        let replica_id = sha256_words_chip.pi_into_words(
            layouter.namespace(|| "decompose replica-id into sha256 words"),
            pi_col,
            Self::REPLICA_ID_ROW,
        )?;

        // Witness `comm_c`, `root_r`, and each challenge's TreeD leaf.
        let (comm_c, root_r, leafs_d) = layouter.assign_region(
            || "witness comm_c and root_r",
            |mut region| {
                let offset = 0;
                let mut advice_iter = AdviceIter::new(offset, advice.clone());

                let comm_c = {
                    let (offset, col) = advice_iter.next().unwrap();
                    region.assign_advice(
                        || "comm_c",
                        col,
                        offset,
                        || priv_inputs.comm_c.ok_or(Error::Synthesis),
                    )?
                };

                let root_r = {
                    let (offset, col) = advice_iter.next().unwrap();
                    region.assign_advice(
                        || "root_r",
                        col,
                        offset,
                        || priv_inputs.root_r.ok_or(Error::Synthesis),
                    )?
                };

                let leafs_d = priv_inputs
                    .challenge_proofs
                    .iter()
                    .enumerate()
                    .map(|(i, challenge_proof)| {
                        let (offset, col) = advice_iter.next().unwrap();
                        region.assign_advice(
                            || format!("challenge {} leaf_d", i),
                            col,
                            offset,
                            || challenge_proof.leaf_d.ok_or(Error::Synthesis),
                        )
                    })
                    .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

                Ok((comm_c, root_r, leafs_d))
            },
        )?;

        // Assign reusable constants that are used to compute each challenge's label.
        let labeling_constants = labeling_chip.assign_constants(&mut layouter)?;

        // Compute `comm_r = H(comm_c, root_r)` and constrain with public input.
        let comm_r = poseidon_2_chip.hash(
            layouter.namespace(|| "calculate comm_r"),
            &[comm_c.clone(), root_r.clone()],
            POSEIDON_CONSTANTS.get::<FieldArity<F, U2>>().unwrap(),
        )?;
        layouter.constrain_instance(comm_r.cell(), pi_col, Self::COMM_R_ROW)?;

        let mut challenges = Vec::<AssignedU32<F>>::with_capacity(Self::CHALLENGE_COUNT);
        let mut challenges_bits = Vec::<[AssignedBit<F>; 32]>::with_capacity(Self::CHALLENGE_COUNT);

        // Assign each challenge as a `u32` and 32 bits.
        for (i, (challenge, pi_row)) in pub_inputs
            .challenges
            .iter()
            .zip(Self::CHALLENGE_ROWS)
            .enumerate()
        {
            let (challenge, challenge_bits) = uint32_chip.witness_assign_bits(
                layouter.namespace(|| format!("assign challenge {} as 32 bits", i)),
                *challenge,
            )?;
            layouter.constrain_instance(challenge.cell(), pi_col, pi_row)?;
            challenges.push(challenge);
            challenges_bits.push(challenge_bits);
        }

        // Verify that each challenge's TreeD merkle proof is consistent with the public CommD.
        for (i, (((challenge, challenge_bits), leaf_d), challenge_proof)) in challenges.iter()
            .zip(challenges_bits.iter())
            .zip(leafs_d.iter())
            .zip(priv_inputs.challenge_proofs.iter())
            .enumerate()
        {
            let comm_d = tree_d_merkle_chip.copy_leaf_compute_root(
                layouter.namespace(|| format!("calculate comm_d from challenge {} merkle proof", i)),
                challenge_bits,
                leaf_d,
                &challenge_proof.path_d,
            )?;
            layouter.constrain_instance(comm_d.cell(), pi_col, Self::COMM_D_ROW)?;

            // Assign parent columns.
            let (drg_parent_columns, exp_parent_columns) = layouter.assign_region(
                || format!("assign parent columns for challenge {}", i),
                |mut region| {
                    let offset = 0;
                    let mut advice_iter = AdviceIter::new(offset, advice.to_vec());

                    let drg_parent_columns = challenge_proof
                        .drg_parent_proofs
                        .iter()
                        .enumerate()
                        .map(|(parent_index, parent_proof)| {
                            parent_proof
                                .column
                                .iter()
                                .enumerate()
                                .map(|(layer_index, label)| {
                                    let (offset, col) = advice_iter.next().unwrap();
                                    region.assign_advice(
                                        || format!(
                                            "challenge {} drg parent {} column layer {}",
                                            i,
                                            parent_index,
                                            layer_index,
                                        ),
                                        col,
                                        offset,
                                        || label.ok_or(Error::Synthesis),
                                    )
                                })
                                .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()
                       })
                        .collect::<Result<Vec<Vec<AssignedCell<F, F>>>, Error>>()?;

                    let exp_parent_columns = challenge_proof
                        .exp_parent_proofs
                        .iter()
                        .enumerate()
                        .map(|(parent_index, parent_proof)| {
                            parent_proof
                                .column
                                .iter()
                                .enumerate()
                                .map(|(layer_index, label)| {
                                    let (offset, col) = advice_iter.next().unwrap();
                                    region.assign_advice(
                                        || format!(
                                            "challenge {} exp parent {} column layer {}",
                                            i,
                                            parent_index,
                                            layer_index,
                                        ),
                                        col,
                                        offset,
                                        || label.ok_or(Error::Synthesis),
                                    )
                                })
                                .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()
                       })
                        .collect::<Result<Vec<Vec<AssignedCell<F, F>>>, Error>>()?;

                    Ok((drg_parent_columns, exp_parent_columns))
                },
            )?;

            // Compute each parent's column digest and verify the parent's TreeC Merkle proof.
            for (parent_index, (parent_column, parent_proof)) in drg_parent_columns
                .iter()
                .zip(challenge_proof.drg_parent_proofs.iter())
                .enumerate()
            {
                let leaf_c = column_hasher_chip.hash(
                    layouter.namespace(|| format!(
                        "challenge {} drg parent {} column digest",
                        i,
                        parent_index,
                    )),
                    parent_column,
                )?;
                let comm_c_calc = tree_r_merkle_chip.copy_leaf_compute_root(
                    layouter.namespace(|| format!(
                        "calculate comm_c from challenge {} drg parent {} merkle proof",
                        i,
                        parent_index,
                    )),
                    challenge_bits,
                    &leaf_c,
                    &parent_proof.path_c,
                )?;
                layouter.assign_region(
                    || format!(
                        "constrain challenge {} drg parent {} comm_c_calc == comm_c",
                        i,
                        parent_index,
                    ),
                    |mut region| region.constrain_equal(comm_c.cell(), comm_c_calc.cell()),
                )?;
            }

            for (parent_index, (parent_column, parent_proof)) in exp_parent_columns
                .iter()
                .zip(challenge_proof.exp_parent_proofs.iter())
                .enumerate()
            {
                let leaf_c = column_hasher_chip.hash(
                    layouter.namespace(|| format!(
                        "challenge {} exp parent {} column digest",
                        i,
                        parent_index,
                    )),
                    parent_column,
                )?;
                let comm_c_calc = tree_r_merkle_chip.copy_leaf_compute_root(
                    layouter.namespace(|| format!(
                        "calculate comm_c from challenge {} exp parent {} merkle proof",
                        i,
                        parent_index,
                    )),
                    challenge_bits,
                    &leaf_c,
                    &parent_proof.path_c,
                )?;
                layouter.assign_region(
                    || format!(
                        "constrain challenge {} exp parent {} comm_c_calc == comm_c",
                        i,
                        parent_index,
                    ),
                    |mut region| region.constrain_equal(comm_c.cell(), comm_c_calc.cell()),
                )?;
            }

            let mut challenge_column = Vec::<AssignedCell<F, F>>::with_capacity(Self::NUM_LAYERS);

            for layer_index in 0..Self::NUM_LAYERS {
                let mut parent_labels: Vec<AssignedU32<F>> = if layer_index == 0 {
                    Vec::with_capacity(DRG_PARENT_LABELS_WORD_LEN)
                } else {
                    Vec::with_capacity(DRG_PARENT_LABELS_WORD_LEN + EXP_PARENT_LABELS_WORD_LEN)
                };

                let drg_parent_labels =
                    drg_parent_columns.iter().map(|parent_col| parent_col[layer_index].clone());

                for (parent_index, parent_label) in drg_parent_labels.enumerate() {
                    let parent_label = sha256_words_chip.copy_into_words(
                        layouter.namespace(|| format!(
                            "challenge {} drg parent {} layer {} label into sha256 words",
                            i,
                            parent_index,
                            layer_index,
                        )),
                        parent_label,
                    )?;
                    parent_labels.extend(parent_label);
                }

                let mut repeated_parent_labels =
                    Vec::<AssignedU32<F>>::with_capacity(REPEATED_PARENT_LABELS_WORD_LEN);

                // Repeat parent labels until it contains 37 parent labels.
                if layer_index == 0 {
                    // 6, 12, 18, 24, 30, 36, 37 parent labels
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels[..LABEL_WORD_LEN]);
                } else {
                    let exp_parent_labels = exp_parent_columns
                        .iter()
                        .map(|parent_col| parent_col[layer_index - 1].clone());

                    for (parent_index, parent_label) in exp_parent_labels.enumerate() {
                        let parent_label = sha256_words_chip.copy_into_words(
                            layouter.namespace(|| format!(
                                "challenge {} exp parent {} layer {} label into sha256 words",
                                i,
                                parent_index,
                                layer_index,
                            )),
                            parent_label,
                        )?;
                        parent_labels.extend(parent_label);
                    }

                    // 14, 28, 37 parent labels
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels);
                    repeated_parent_labels.extend_from_slice(&parent_labels[..9 * LABEL_WORD_LEN]);
                }

                // Compute the challenge's layer label:
                let label = labeling_chip.label(
                    layouter.namespace(|| format!("challenge {} layer {} create label", i, layer_index)),
                    layer_index,
                    &labeling_constants,
                    &replica_id,
                    &challenge,
                    &repeated_parent_labels,
                )?;
                challenge_column.push(label);
            }

            // Compute the challenge's column digest.
            let leaf_c = column_hasher_chip.hash(
                layouter.namespace(|| format!("challenge {} column digest", i)),
                &challenge_column,
            )?;
            // Verify the challenge's TreeC Merkle proof.
            let comm_c_calc = tree_r_merkle_chip.copy_leaf_compute_root(
                layouter.namespace(|| format!(
                    "challenge {} calculate comm_c from merkle proof",
                    i,
                )),
                challenge_bits,
                &leaf_c,
                &challenge_proof.path_c,
            )?;
            layouter.assign_region(
                || format!("constrain challenge {} comm_c_calc == comm_c", i),
                |mut region| region.constrain_equal(comm_c.cell(), comm_c_calc.cell()),
            )?;

            // Compute the challenge's encoding (i.e. its TreeR leaf): `leaf_r = leaf_d + key`,
            // where the encoding key is the challenge's last layer label.
            let key = &challenge_column[Self::NUM_LAYERS - 1];
            let leaf_r = encoding_chip
                .encode(layouter.namespace(|| format!("encode challenge {}", i)), leaf_d, key)?;

            // Verify the challenge's TreeR Merkle proof.
            let comm_r_calc = tree_r_merkle_chip.copy_leaf_compute_root(
                layouter.namespace(|| format!(
                    "challenge {} calculate comm_r from merkle proof",
                    i,
                )),
                challenge_bits,
                &leaf_r,
                &challenge_proof.path_r,
            )?;
            layouter.assign_region(
                || format!("constrain challenge {} comm_r_calc == comm_r", i),
                |mut region| region.constrain_equal(comm_r.cell(), comm_r_calc.cell()),
            )?;
        }

        Ok(())
    }
}
