#![allow(non_snake_case)]
use crate::miller_loop_native::SIX_U_PLUS_2_NAF;
use ark_bn254::{Fq, Fq2};
use ark_ff::Field;
use ark_std::One;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::witness::PartitionWitness;
use plonky2::util::serialization::{Read, Write};
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bn254::curves::{g1curve_target::G1Target, g2curve_target::G2Target};
use plonky2_bn254::fields::fq12_target::Fq12Target;
use plonky2_bn254::fields::native::{from_biguint_to_fq, MyFq12};
use plonky2_bn254::fields::{fq2_target::Fq2Target, fq_target::FqTarget};
use plonky2_ecdsa::gadgets::biguint::{GeneratedValuesBigUint, WitnessBigUint};

const XI_0: usize = 9;

fn sparse_line_function_unequal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: (&G2Target<F, D>, &G2Target<F, D>),
    P: &G1Target<F, D>,
) -> Vec<Option<Fq2Target<F, D>>> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);
    let y1_minus_y2 = y_1.sub(builder, &y_2);
    let x2_minus_x1 = x_2.sub(builder, &x_1);
    let x1y2 = x_1.mul(builder, &y_2);
    let x2y1 = x_2.mul(builder, &y_1);
    let out3 = y1_minus_y2.mul_scalar(builder, &x);
    let out2 = x2_minus_x1.mul_scalar(builder, &y);
    let out5 = x1y2.sub(builder, &x2y1);

    vec![None, None, Some(out2), Some(out3), None, Some(out5)]
}

fn sparse_line_function_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Vec<Option<Fq2Target<F, D>>> {
    let (x, y) = (&Q.x, &Q.y);
    let x_sq = x.mul(builder, &x);
    let x_cube = x_sq.mul(builder, &x);
    let three_x_cu = x_cube.mul_scalar_const(builder, &Fq::from(3));
    let y_sq = y.mul(builder, &y);
    let two_y_sq = y_sq.mul_scalar_const(builder, &Fq::from(2));
    let out0_left = three_x_cu.sub(builder, &two_y_sq);
    let out0 = out0_left.mul_w6::<XI_0>(builder);
    let x_sq_px = x_sq.mul_scalar(builder, &P.x);
    let out4 = x_sq_px.mul_scalar_const(builder, &Fq::from(-3));
    let y_py = y.mul_scalar(builder, &P.y);
    let out3 = y_py.mul_scalar_const(builder, &Fq::from(2));

    vec![Some(out0), None, None, Some(out3), Some(out4), None]
}

#[derive(Debug)]
pub struct SparseFp12MulGenerator<F: RichField + Extendable<D>, const D: usize> {
    a: Fq12Target<F, D>,
    b: Vec<Fq2Target<F, D>>,
    sparse_map: Vec<bool>,
    mul: Fq12Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for SparseFp12MulGenerator<F, D>
{
    fn id(&self) -> String {
        "SparseFp12MulGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut deps = self
            .a
            .coeffs
            .iter()
            .flat_map(|coeff| coeff.target.value.limbs.iter().map(|&l| l.0))
            .collect_vec();

        for fq2_target in &self.b {
            deps.extend(
                fq2_target
                    .coeffs
                    .iter()
                    .flat_map(|coeff| coeff.target.value.limbs.iter().map(|&l| l.0)),
            );
        }

        deps
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let mut a_fp2_coeffs = Vec::with_capacity(6);
        for i in 0..6 {
            let c0 = from_biguint_to_fq(
                witness.get_biguint_target(self.a.coeffs[i].target.value.clone()),
            );
            let c1 = from_biguint_to_fq(
                witness.get_biguint_target(self.a.coeffs[i + 6].target.value.clone()),
            );
            a_fp2_coeffs.push(Fq2::new(c0, c1));
        }

        let mut b_val = Vec::with_capacity(self.b.len());
        for b_target in self.b.iter() {
            let c0 = from_biguint_to_fq(
                witness.get_biguint_target(b_target.coeffs[0].target.value.clone()),
            );
            let c1 = from_biguint_to_fq(
                witness.get_biguint_target(b_target.coeffs[1].target.value.clone()),
            );
            b_val.push(Fq2 { c0, c1 });
        }

        let mut prod_2d: Vec<Option<Fq2>> = vec![None; 11];
        for i in 0..6 {
            let mut idx = 0;
            for j in 0..6 {
                let mut cur_b: Option<Fq2> = None;
                if self.sparse_map[j] {
                    cur_b = Some(b_val[idx]);
                    idx += 1;
                } else {
                    cur_b = None;
                }
                prod_2d[i + j] = match (prod_2d[i + j].clone(), &a_fp2_coeffs[i], cur_b.as_ref()) {
                    (a, _, None) => a,
                    (None, a, Some(b)) => {
                        let ab = a * b;
                        Some(ab)
                    }
                    (Some(a), b, Some(c)) => {
                        let bc = b * c;
                        let out = a + bc;
                        Some(out)
                    }
                }
            }
        }

        let mut out_fp2 = Vec::with_capacity(6);
        for i in 0..6 {
            let prod = if i != 5 {
                let eval_w6 = prod_2d[i + 6]
                    .as_ref()
                    .map(|a| a * Fq2::new(Fq::from(9), Fq::ONE));
                match (prod_2d[i].as_ref(), eval_w6) {
                    (None, b) => b.unwrap(),
                    (Some(a), None) => a.clone(),
                    (Some(a), Some(b)) => a + b,
                }
            } else {
                prod_2d[i].clone().unwrap()
            };
            out_fp2.push(prod);
        }

        let mut out_coeffs = Vec::with_capacity(12);
        for fp2_coeff in &out_fp2 {
            out_coeffs.push(fp2_coeff.c0.into());
        }
        for fp2_coeff in &out_fp2 {
            out_coeffs.push(fp2_coeff.c1.into());
        }

        let out = MyFq12 {
            coeffs: out_coeffs.try_into().unwrap(),
        };
        let out_biguint: Vec<BigUint> = out
            .coeffs
            .iter()
            .cloned()
            .map(|coeff| coeff.into())
            .collect_vec();

        for i in 0..12 {
            out_buffer.set_biguint_target(&self.mul.coeffs[i].target.value, &out_biguint[i]);
        }
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>,
    ) -> plonky2::util::serialization::IoResult<()> {
        self.a.serialize(dst, common_data)?;
        self.mul.serialize(dst, common_data)?;
        dst.write_usize(self.b.len())?;
        for fq2 in &self.b {
            fq2.serialize(dst, common_data)?;
        }
        dst.write_usize(self.sparse_map.len())?;
        for flag in &self.sparse_map {
            dst.write_bool(*flag)?;
        }

        Ok(())
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>,
    ) -> plonky2::util::serialization::IoResult<Self>
    where
        Self: Sized,
    {
        let a = Fq12Target::deserialize(src, common_data)?;
        let mul = Fq12Target::deserialize(src, common_data)?;
        let b_len = src.read_usize()?;
        let b = (0..b_len)
            .map(|_| Fq2Target::deserialize(src, common_data))
            .collect::<Result<Vec<_>, _>>()?;
        let sparse_map_len = src.read_usize()?;
        let sparse_map = (0..sparse_map_len)
            .map(|_| src.read_bool())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            a,
            b,
            mul,
            sparse_map,
        })
    }
}

fn sparse_fp12_multiply<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
    b: Vec<Option<Fq2Target<F, D>>>,
) -> Fq12Target<F, D> {
    let mul = Fq12Target::empty(builder);

    let mut sparse_map = Vec::with_capacity(b.len());
    let mut b_targets = Vec::new();
    for maybe_fq2_target in b {
        if let Some(fq2_target) = maybe_fq2_target {
            sparse_map.push(true);
            b_targets.push(fq2_target);
        } else {
            sparse_map.push(false);
        }
    }
    builder.add_simple_generator(SparseFp12MulGenerator::<F, D> {
        a: a.clone(),
        b: b_targets,
        sparse_map,
        mul: mul.clone(),
    });

    mul
}

fn fp12_multiply_with_line_unequal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    g: &Fq12Target<F, D>,
    Q: (&G2Target<F, D>, &G2Target<F, D>),
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    let line = sparse_line_function_unequal(builder, Q, P);
    sparse_fp12_multiply(builder, g, line)
}

fn fp12_multiply_with_line_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    g: &Fq12Target<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    let line = sparse_line_function_equal(builder, Q, P);
    sparse_fp12_multiply(builder, g, line)
}

fn miller_loop_BN<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
    pseudo_binary_encoding: &[i8],
) -> Fq12Target<F, D> {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 {
        Q.clone()
    } else {
        Q.neg(builder)
    };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal(builder, &R, P);
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = FqTarget::constant(builder, Fq::ZERO);
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[0].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[1].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }

    let mut f = Fq12Target {
        coeffs: f_coeffs.try_into().unwrap(),
    };

    loop {
        if i != last_index - 1 {
            let f_sq = f.mul(builder, &f);
            f = fp12_multiply_with_line_equal(builder, &f_sq, &R, P);
        }

        R = R.double(builder);

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = if pseudo_binary_encoding[i] == 1 {
                Q.clone()
            } else {
                Q.neg(builder)
            };
            f = fp12_multiply_with_line_unequal(builder, &f, (&R, &sign_Q), P);
            R = R.add(builder, &sign_Q);
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(9), Fq::one()).pow(k.to_u64_digits());
    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;
    let c2 = Fq2Target::constant(builder, c2);
    let c3 = Fq2Target::constant(builder, c3);

    let Q_1 = twisted_frobenius(builder, Q, c2.clone(), c3.clone());
    let neg_Q_2 = neg_twisted_frobenius(builder, &Q_1, c2.clone(), c3.clone());
    f = fp12_multiply_with_line_unequal(builder, &f, (&R, &Q_1), P);
    R = R.add(builder, &Q_1);
    f = fp12_multiply_with_line_unequal(builder, &f, (&R, &neg_Q_2), P);

    f
}

fn multi_miller_loop_BN<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pairs: Vec<(&G1Target<F, D>, &G2Target<F, D>)>,
    pseudo_binary_encoding: &[i8],
) -> Fq12Target<F, D> {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert_eq!(pseudo_binary_encoding[last_index], 1);

    let neg_b: Vec<G2Target<F, D>> = pairs.iter().map(|pair| pair.1.neg(builder)).collect();

    // initialize the first line function into Fq12 point
    let mut f = {
        let sparse_f = sparse_line_function_equal(builder, pairs[0].1, pairs[0].0);
        assert_eq!(sparse_f.len(), 6);

        let zero_fp = FqTarget::constant(builder, Fq::ZERO);
        let mut f_coeffs = Vec::with_capacity(12);
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.coeffs[0].clone());
            } else {
                f_coeffs.push(zero_fp.clone());
            }
        }
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.coeffs[1].clone());
            } else {
                f_coeffs.push(zero_fp.clone());
            }
        }
        Fq12Target {
            coeffs: f_coeffs.try_into().unwrap(),
        }
    };

    for &(a, b) in pairs.iter().skip(1) {
        f = fp12_multiply_with_line_equal(builder, &f, b, a);
    }

    i -= 1;
    let mut r = pairs.iter().map(|pair| pair.1.clone()).collect::<Vec<_>>();
    loop {
        if i != last_index - 1 {
            f = f.mul(builder, &f);
            for (r, &(a, _)) in r.iter().zip(pairs.iter()) {
                f = fp12_multiply_with_line_equal(builder, &f, r, a);
            }
        }
        for r in r.iter_mut() {
            *r = r.double(builder);
        }

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            for ((r, neg_b), &(a, b)) in r.iter_mut().zip(neg_b.iter()).zip(pairs.iter()) {
                let sign_b = if pseudo_binary_encoding[i] == 1 {
                    b
                } else {
                    neg_b
                };
                f = fp12_multiply_with_line_unequal(builder, &f, (r, sign_b), a);
                *r = r.add(builder, &sign_b);
            }
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(9), Fq::one()).pow(k.to_u64_digits());

    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;
    let c2 = Fq2Target::constant(builder, c2);
    let c3 = Fq2Target::constant(builder, c3);

    // finish multiplying remaining line functions outside the loop
    for (r, &(a, b)) in r.iter_mut().zip(pairs.iter()) {
        let b_1 = twisted_frobenius(builder, &b, c2.clone(), c3.clone());
        let neg_b_2 = neg_twisted_frobenius(builder, &b_1, c2.clone(), c3.clone());
        f = fp12_multiply_with_line_unequal(builder, &f, (r, &b_1), a);
        // *r = (r.clone() + b_1).into();
        *r = r.add(builder, &b_1);
        f = fp12_multiply_with_line_unequal(builder, &f, (r, &neg_b_2), a);
    }
    f
}

fn twisted_frobenius<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    c2: Fq2Target<F, D>,
    c3: Fq2Target<F, D>,
) -> G2Target<F, D> {
    let frob_x = Q.x.conjugate(builder);
    let frob_y = Q.y.conjugate(builder);
    let out_x = c2.mul(builder, &frob_x);
    let out_y = c3.mul(builder, &frob_y);
    G2Target::new(out_x, out_y)
}

fn neg_twisted_frobenius<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    c2: Fq2Target<F, D>,
    c3: Fq2Target<F, D>,
) -> G2Target<F, D> {
    let frob_x = Q.x.conjugate(builder);
    let neg_frob_y = Q.y.neg_conjugate(builder);
    let out_x = c2.mul(builder, &frob_x);
    let out_y = c3.mul(builder, &neg_frob_y);
    G2Target::new(out_x, out_y)
}

pub fn miller_loop_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    miller_loop_BN(builder, Q, P, &SIX_U_PLUS_2_NAF)
}

pub fn multi_miller_loop_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pairs: Vec<(&G1Target<F, D>, &G2Target<F, D>)>,
) -> Fq12Target<F, D> {
    multi_miller_loop_BN(builder, pairs, &SIX_U_PLUS_2_NAF)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::miller_loop_circuit;
    use crate::{
        miller_loop_native::{miller_loop_native, multi_miller_loop_native},
        miller_loop_target::multi_miller_loop_circuit,
    };
    use plonky2_bn254::{
        curves::{g1curve_target::G1Target, g2curve_target::G2Target},
        fields::fq12_target::Fq12Target,
    };

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_miller_loop_target() {
        let rng = &mut rand::thread_rng();
        let Q = G2Affine::rand(rng);
        let P = G1Affine::rand(rng);
        let r_expected = miller_loop_native(&Q, &P);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let Q_t = G2Target::constant(&mut builder, Q);
        let P_t = G1Target::constant(&mut builder, P);

        let r_t = miller_loop_circuit(&mut builder, &Q_t, &P_t);
        let r_expected_t = Fq12Target::constant(&mut builder, r_expected.into());

        Fq12Target::connect(&mut builder, &r_t, &r_expected_t);

        let pw = PartialWitness::<F>::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let now = Instant::now();
        let _proof = data.prove(pw);
        println!("proving time: {:?}", now.elapsed());
    }

    #[test]
    fn test_multi_miller_loop_target() {
        let rng = &mut rand::thread_rng();
        let Q0 = G2Affine::rand(rng);
        let P0 = G1Affine::rand(rng);
        let Q1 = G2Affine::rand(rng);
        let P1 = G1Affine::rand(rng);

        let r_expected = multi_miller_loop_native(vec![(&P0, &Q0), (&P1, &Q1)]);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let Q0_t = G2Target::constant(&mut builder, Q0);
        let P0_t = G1Target::constant(&mut builder, P0);
        let Q1_t = G2Target::constant(&mut builder, Q1);
        let P1_t = G1Target::constant(&mut builder, P1);

        let r_t = multi_miller_loop_circuit(&mut builder, vec![(&P0_t, &Q0_t), (&P1_t, &Q1_t)]);
        let r_expected_t = Fq12Target::constant(&mut builder, r_expected.into());

        Fq12Target::connect(&mut builder, &r_t, &r_expected_t);

        let pw = PartialWitness::<F>::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
