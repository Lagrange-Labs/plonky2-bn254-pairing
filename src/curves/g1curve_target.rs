use ark_bn254::G1Affine;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::fields::fq_target::FqTarget;

#[derive(Clone, Debug)]
pub struct G1Target<F: RichField + Extendable<D>, const D: usize> {
    pub x: FqTarget<F, D>,
    pub y: FqTarget<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G1Target<F, D> {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = FqTarget::new(builder);
        let y = FqTarget::new(builder);
        G1Target { x, y }
    }

    pub fn construct(x: FqTarget<F, D>, y: FqTarget<F, D>) -> Self {
        G1Target { x, y }
    }

    pub fn constant(builder: &mut CircuitBuilder<F, D>, a: G1Affine) -> Self {
        let x = a.x;
        let y = a.y;

        let x_target = FqTarget::constant(builder, x);
        let y_target = FqTarget::constant(builder, y);

        G1Target {
            x: x_target,
            y: y_target,
        }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        FqTarget::connect(builder, &lhs.x, &rhs.x);
        FqTarget::connect(builder, &lhs.y, &rhs.y);
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = self.x.clone();
        let y = self.y.neg(builder);
        G1Target { x, y }
    }

    pub fn double(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = self.x.clone();
        let y = self.y.clone();
        let double_y = y.add(builder, &y);
        let inv_double_y = double_y.inv(builder);
        let x_squared = x.mul(builder, &x);
        let double_x_squared = x_squared.add(builder, &x_squared);
        let triple_x_squared = double_x_squared.add(builder, &x_squared);
        let triple_xx_a = triple_x_squared.clone();
        let lambda = triple_xx_a.mul(builder, &inv_double_y);
        let lambda_squared = lambda.mul(builder, &lambda);
        let x_double = x.add(builder, &x);
        let x3 = lambda_squared.sub(builder, &x_double);
        let x_diff = x.sub(builder, &x3);
        let lambda_x_diff = lambda.mul(builder, &x_diff);
        let y3 = lambda_x_diff.sub(builder, &y);

        G1Target { x: x3, y: y3 }
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let x1 = self.x.clone();
        let y1 = self.y.clone();
        let x2 = rhs.x.clone();
        let y2 = rhs.y.clone();

        let u = y2.sub(builder, &y1);
        let v = x2.sub(builder, &x1);
        let v_inv = v.inv(builder);
        let s = u.mul(builder, &v_inv);
        let s_squared = s.mul(builder, &s);
        let x_sum = x2.add(builder, &x1);
        let x3 = s_squared.sub(builder, &x_sum);
        let x_diff = x1.sub(builder, &x3);
        let prod = s.mul(builder, &x_diff);
        let y3 = prod.sub(builder, &y1);

        G1Target { x: x3, y: y3 }
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::G1Affine;
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::G1Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_g1_add() {
        let rng = &mut rand::thread_rng();
        let a = G1Affine::rand(rng);
        let b = G1Affine::rand(rng);
        let c_expected: G1Affine = (a + b).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = G1Target::constant(&mut builder, a);
        let b_t = G1Target::constant(&mut builder, b);
        let c_t = a_t.add(&mut builder, &b_t);
        let c_expected_t = G1Target::constant(&mut builder, c_expected);

        G1Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_g1_double() {
        let rng = &mut rand::thread_rng();
        let a = G1Affine::rand(rng);
        let c_expected: G1Affine = (a + a).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = G1Target::constant(&mut builder, a);
        let c_t = a_t.double(&mut builder);
        let c_expected_t = G1Target::constant(&mut builder, c_expected);

        G1Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }
}
