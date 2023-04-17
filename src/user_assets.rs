use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector, Expression, keygen_pk, keygen_vk, create_proof, verify_proof
    },
    poly::{
        Rotation,
        kzg::{commitment::{ParamsKZG, KZGCommitmentScheme}, multiopen::{ProverGWC, VerifierGWC}, strategy::SingleStrategy},
        commitment::ParamsProver,
    },
    halo2curves::bn256::{Bn256, Fr as Fp},
    transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer, self, Blake2bRead, TranscriptReadBuffer}
};
// use halo2curves::pasta_curves::EqAffine;
use std::marker::PhantomData;
use rand_core::OsRng;

static MAX_BITS: i32 = -4;
// static NUM_USERS: u32 = 4;

#[derive(Debug, Clone)]
struct R1CSConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    sel: [Selector; 5],
    c_pi: Column<Instance>,
}

#[derive(Debug, Clone)]
struct R1CSChip<F: FieldExt> {
    // config: R1CSConfig,
    marker: PhantomData<F>,
}

impl<F: FieldExt> R1CSChip<F> {
    // fn construct(config: R1CSConfig) -> Self {
    //     R1CSChip {
    //         config,
    //         marker: PhantomData,
    //     }
    // }

    fn configure(meta: &mut ConstraintSystem<F>) -> R1CSConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();

        let s0 = meta.selector();
        let s1 = meta.selector();
        let s2 = meta.selector();
        let s3 = meta.selector();
        let s4 = meta.selector();

        let col_pi = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_pi);

        meta.create_gate("a=b", |meta| {
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let s = meta.query_selector(s0);
            vec![s*(a-b)]
        });

        meta.create_gate("b init binary", |meta| {
            let b = meta.query_advice(col_b, Rotation::cur());
            let s = meta.query_selector(s1);
            vec![s*b.clone()*(b-Expression::Constant(F::one()))]
        });

        meta.create_gate("b extends bit", |meta| {
            let b = meta.query_advice(col_b, Rotation::cur());
            let b_prev = meta.query_advice(col_b, Rotation::prev());
            let s = meta.query_selector(s2);
            vec![s*(b.clone()-Expression::Constant(F::from(2))*b_prev.clone())*(b-Expression::Constant(F::from(2))*b_prev-Expression::Constant(F::one()))]
        });

        meta.create_gate("b init cumulative sum", |meta| {
            let b = meta.query_advice(col_b, Rotation::cur());
            let b_prev = meta.query_advice(col_b, Rotation::prev());
            let s = meta.query_selector(s3);
            vec![s*(b-b_prev)]
        });

        meta.create_gate("b cumulative sum", |meta| {
            let b = meta.query_advice(col_b, Rotation::cur());
            let b_prev = meta.query_advice(col_b, Rotation::prev());
            let b_prev_cum = meta.query_advice(col_b, Rotation(MAX_BITS-1));
            let s = meta.query_selector(s4);
            vec![s*(b-b_prev-b_prev_cum)]
        });

        R1CSConfig { a: col_a, b: col_b, sel: [s0, s1, s2, s3, s4], c_pi: col_pi }
    }
}

#[derive(Default)]
struct R1CSCircuit<F> {
    a: Vec<F>,
    b: Vec<F>,
    sel: [Vec<bool>; 5],
}

impl<F: FieldExt> Circuit<F> for R1CSCircuit<F> {
    type Config = R1CSConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        R1CSChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let len = self.a.len();
        layouter.assign_region(
            || "a and b",
            |mut region| {
                for i in 0..len-1 {
                    region.assign_advice(
                        || "a",
                        config.a,
                        i,
                        || Value::known(self.a[i])
                    )?;
                    region.assign_advice(
                        || "b",
                        config.b,
                        i,
                        || Value::known(self.b[i])
                    )?;
                    for j in 0..5 {
                        if self.sel[j][i] {
                            config.sel[j].enable(&mut region, i)?;
                        }
                    }
                }
                region.assign_advice(
                    || "a",
                    config.a,
                    len-1,
                    || Value::known(self.a[len-1])
                )?;
                region.assign_advice_from_instance(
                    || "b",
                    config.c_pi,
                    0,
                    config.b,
                    len-1
                )?;
                for j in 0..5 {
                    if self.sel[j][len-1] {
                        config.sel[j].enable(&mut region, len-1)?;
                    }
                }
                Ok(())
            }
        )?;

        Ok(())
    }
}

// all user balances are < 2^k.
fn balance_2_pow_k(nums: &[u64]) -> u32 {
    let max_num = nums.iter().cloned().max().unwrap_or(0);
    let k = f64::log2(max_num as f64).floor() as u32 + 1;
    assert!(k == -MAX_BITS as u32, "user balances exceed MAX_BITS");
    k
}

fn prepare_columns(user_hashes: &[u64], user_bal: &[u64]) -> (Vec<u64>, Vec<u64>, [Vec<bool>; 5]) {
    let k = balance_2_pow_k(user_bal);
    dbg!(k);

    let len = ((k+1)*(user_hashes.len() as u32)) as usize;
    let mut p: Vec<u64> = vec![0; len];
    let mut aux: Vec<u64> = vec![0; len];
    let mut sel = [vec![false; len], vec![false; len], vec![false; len], vec![false; len], vec![false; len]];

    let mut cumulative_sum = 0;
    for i in 0..user_hashes.len() {
        cumulative_sum += user_bal[i];
        let mut last_idx = i*(k as usize+1)+k as usize;

        aux[last_idx] = cumulative_sum;
        if i==0 {
            sel[3][last_idx] = true;
        } else {
            sel[4][last_idx] = true;
        }

        aux[last_idx-1] = user_bal[i];
        p[last_idx-1] = user_bal[i];
        sel[0][last_idx-1] = true; // selector for user balance match

        p[last_idx-2] = user_hashes[i];

        last_idx -= 1;
        for _ in (0 as usize)..((k-1) as usize) {
            last_idx -= 1;
            aux[last_idx] = aux[last_idx+1]/2;
            sel[2][last_idx+1] = true; // aux extends by 1 bit from previous
        }

        sel[1][last_idx] = true; // selector for initial aux value to be binary
    }

    (p,aux,sel)
}

fn prove(k: u32, user_hashes: Vec<u64>, user_bal: Vec<u64>) -> Result<(), Error> {
    let total_balance: u64 = user_bal.iter().sum();

    let params: ParamsKZG<Bn256> = ParamsKZG::<Bn256>::new(k);
    let (p, aux, sel) = prepare_columns(&user_hashes, &user_bal);
    let p_fp: Vec<Fp> = p.iter().map(|&num| Fp::from(num)).collect();
    let aux_fp: Vec<Fp> = aux.iter().map(|&num| Fp::from(num)).collect();

    let circuit = R1CSCircuit {
        a: p_fp,
        b: aux_fp,
        sel: sel,
    };

    let vk = keygen_vk(&params, &circuit).expect("keygen_vk failed");

    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk failed");

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[&[&vec![Fp::from(total_balance)]]],
        OsRng,
        &mut transcript,
    ).expect("proof gen failed");

    let proof = transcript.finalize();

    let transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let strategy = SingleStrategy::new(&params);

    verify_proof::<_, VerifierGWC<Bn256>, _, _, _>(
        &params,
        pk.get_vk(),
        strategy.clone(),
        &[&[&vec![Fp::from(total_balance)]]],
        &mut transcript.clone()
    ).unwrap();
    Ok(())

}

#[cfg(test)]
mod tests {
    use super::R1CSCircuit;
    use crate::user_assets::{prepare_columns, prove};
    use halo2_proofs::halo2curves::bn256::Fr as Fp;


    #[test]
    fn test_r1cs() {
        //env::set_var("RUST_BACKTRACE", "full");
        use halo2_proofs::dev::MockProver;

        let k = 5;
        let user_hashes: Vec<u64> = vec![1, 2, 3];
        let user_bal: Vec<u64> = vec![3, 4, 10];

        let total_balance: u64 = user_bal.iter().sum();

        let (p, aux, sel) = prepare_columns(&user_hashes, &user_bal);
        assert_eq!(p.len(), aux.len());

        for i in 0..p.len() {
            println!("{:?} {:?} {:?} {:?} {:?} {:?} {:?}", p[i], aux[i], sel[0][i], sel[1][i], sel[2][i], sel[3][i], sel[4][i]);
        }

        let p_fp: Vec<Fp> = p.iter().map(|&num| Fp::from(num)).collect();
        let aux_fp: Vec<Fp> = aux.iter().map(|&num| Fp::from(num)).collect();

        let circuit = R1CSCircuit {
            a: p_fp,
            b: aux_fp,
            sel: sel,
        };

        let public_inputs = vec![Fp::from(total_balance)];

        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_keygen() {
        let k = 5;
        let user_hashes: Vec<u64> = vec![1, 2, 3];
        let user_bal: Vec<u64> = vec![3, 4, 10];

        assert!(prove(k, user_hashes, user_bal).is_ok());
    }
}