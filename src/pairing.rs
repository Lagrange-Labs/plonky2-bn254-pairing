use ark_bn254::{Fq12, G1Affine, G2Affine};
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
};
use plonky2_bn254::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::fq12_target::Fq12Target,
};

use crate::{
    final_exp_native::final_exp_native, final_exp_target::final_exp_circuit,
    miller_loop_native::miller_loop_native, miller_loop_target::miller_loop_circuit,
};

pub fn pairing(p: G1Affine, q: G2Affine) -> Fq12 {
    final_exp_native(miller_loop_native(&q, &p)).into()
}

pub fn pairing_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    p: G1Target<F, D>,
    q: G2Target<F, D>,
) -> Fq12Target<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let f = miller_loop_circuit(builder, &q, &p);
    final_exp_circuit::<F, C, D>(builder, f)
}

#[cfg(test)]
mod test {
    use std::time::Instant;

    use ark_bn254::{Bn254, G1Affine, G2Affine};
    use ark_ec::{pairing::Pairing, AffineRepr};
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::curves::{g1curve_target::G1Target, g2curve_target::G2Target};

    use crate::{
        final_exp_native::final_exp_native,
        miller_loop_native::miller_loop_native,
        pairing::{pairing, pairing_circuit},
    };

    #[test]
    fn test_pairing_circuit() {
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;

        let rng = &mut rand::thread_rng();
        let p = G1Affine::rand(rng);
        let q = G2Affine::rand(rng);
        let output = pairing(p, q);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let p_t = G1Target::constant(&mut builder, p);
        let q_t = G2Target::constant(&mut builder, q);
        let output_t = pairing_circuit::<F, C, D>(&mut builder, p_t, q_t);

        let data = builder.build::<C>();
        let now = Instant::now();
        let mut pw = PartialWitness::<F>::new();
        output_t.set_witness(&mut pw, &output);
        let _proof = data.prove(pw).unwrap();
        println!("proving time: {:?}", now.elapsed());
    }

    #[test]
    fn test_pairing_with_arkworks() {
        let rng = &mut rand::thread_rng();
        let p = G1Affine::rand(rng);
        let q = G2Affine::rand(rng);
        let output = pairing(p, q);
        let exp_output = Bn254::pairing(p, q);
        assert_eq!(output, exp_output.0);
    }

    // #[test]
    // fn test_miller_loop_with_arkworks() {
    //     let rng = &mut rand::thread_rng();
    //     let p = G1Affine::rand(rng);
    //     let q = G2Affine::rand(rng);
    //     let output = miller_loop_native(&q, &p);
    //     let exp_output = Bn254::miller_loop(p, q);
    //     assert_eq!(output, exp_output.0.into());
    // }

    #[test]
    fn test_final_exp_with_arkworks() {
        let rng = &mut rand::thread_rng();
        let p = G1Affine::rand(rng);
        let q = G2Affine::rand(rng);
        let rand_fq12 = Bn254::miller_loop(p, q);
        let output = final_exp_native(rand_fq12.0.into());
        let exp_output = Bn254::final_exponentiation(rand_fq12);
        assert_eq!(output, exp_output.unwrap().0.into());
    }
}
