#![allow(non_snake_case)]

use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError,
};
use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use num_bigint::BigInt;
use pasta_curves::{
    arithmetic::CurveAffine,
    group::{ff::PrimeFieldBits, Curve},
    pallas::Point,
};
use utils::f_to_nat;
mod utils;

#[cfg(test)]
mod test_em;

#[derive(Clone)]
pub struct PallasFpParams;

impl EmulatedFieldParams for PallasFpParams {
    fn num_limbs() -> usize {
        5
    }

    fn bits_per_limb() -> usize {
        51
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"40000000000000000000000000000000224698FC094CF91B992D30ED00000001",
            16,
        )
        .unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        None
    }
}

pub type PallasFp<F> = EmulatedFieldElement<F, PallasFpParams>;

pub fn alloc_num_equals<F: PrimeFieldBits, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &PallasFp<F>,
    b: &PallasFp<F>,
) -> Result<AllocatedBit, SynthesisError> {
    let sub = a.sub(&mut cs.namespace(|| "a - b"), b)?;
    PallasFp::alloc_is_zero(&sub, &mut cs.namespace(|| "a == b"))
}

/// Represents an affine point on Pallas curve.
///
/// Point at infinity is represented with (0, 0)
#[derive(Clone)]
pub struct AllocatedAffinePoint<F: PrimeFieldBits> {
    x: PallasFp<F>,
    y: PallasFp<F>,
}

impl<F: PrimeFieldBits> AllocatedAffinePoint<F> {
    /// Produce a point at infinity
    pub fn identity<CS: ConstraintSystem<F>>(mut cs: CS) -> Result<Self, SynthesisError> {
        // (0,0) is the point at infinity
        let x = PallasFp::zero().allocate_field_element_unchecked(&mut cs.namespace(|| "x"))?;
        let y = PallasFp::zero().allocate_field_element_unchecked(&mut cs.namespace(|| "y"))?;
        Ok(Self { x, y })
    }

    /// Allocate a point on the curve
    ///
    /// If the point is not on the curve, it will be treated as the point at infinity (0,0)
    pub fn alloc<CS: ConstraintSystem<F>>(
        mut cs: CS,
        point: &Point,
    ) -> Result<Self, SynthesisError> {
        let coordinates = point.to_affine().coordinates();

        let val = if coordinates.is_some().unwrap_u8() == 1 {
            let x = PallasFp::from(&f_to_nat(coordinates.unwrap().x()));
            let y = PallasFp::from(&f_to_nat(coordinates.unwrap().y()));

            let x = x.allocate_field_element_unchecked(&mut cs.namespace(|| "x"))?;
            let y = y.allocate_field_element_unchecked(&mut cs.namespace(|| "y"))?;
            Self { x, y }
        } else {
            Self::identity(cs.namespace(|| "identity"))?
        };

        Ok(val)
    }

    /// Negates the provided point
    pub fn negate<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        let y = self.y.neg(&mut cs.namespace(|| "y = - self.y"))?;

        Ok(Self {
            x: self.x.clone(),
            y,
        })
    }

    /// Check if the point is the point at infinity
    pub fn alloc_is_identity<CS>(&self, cs: &mut CS) -> Result<AllocatedBit, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x = self.x.alloc_is_zero(&mut cs.namespace(|| "x =? 0"))?;
        let y = self.y.alloc_is_zero(&mut cs.namespace(|| "y =? 0"))?;
        AllocatedBit::and(&mut cs.namespace(|| "and(x, y)"), &x, &y)
    }

    /// Check if two points are equal
    pub fn assert_equal<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &Self,
        b: &Self,
    ) -> Result<(), SynthesisError> {
        PallasFp::assert_is_equal(&mut cs.namespace(|| "x"), &a.x, &b.x)?;
        PallasFp::assert_is_equal(&mut cs.namespace(|| "y"), &a.y, &b.y)?;

        Ok(())
    }

    /// Reduce limbs to match the field modulus
    pub fn reduce<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        let x = self.x.reduce(&mut cs.namespace(|| "x <- x.reduce()"))?;
        let y = self.y.reduce(&mut cs.namespace(|| "y <- y.reduce()"))?;
        Ok(Self { x, y })
    }

    /// Double a point assuming it is not the point at infinity
    pub fn double<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        A: &PallasFp<F>,
    ) -> Result<Self, SynthesisError> {
        //*************************************************************/
        // lambda = (G::Base::from(3) * self.x * self.x + G::GG::A())
        //  * (G::Base::from(2)) * self.y).invert().unwrap();
        /*************************************************************/

        // Compute tmp_ = (G::Base::ONE + G::Base::ONE)* self.y
        let tmp_actual = self.y.add(&mut cs.namespace(|| "tmp_actual"), &self.y)?;
        let one = PallasFp::one().allocate_field_element_unchecked(&mut cs.namespace(|| "one"))?;
        let self_is_identity = self.alloc_is_identity(&mut cs.namespace(|| "self_is_identity"))?;

        let tmp = PallasFp::conditionally_select(
            &mut cs.namespace(|| "tmp"),
            &tmp_actual,
            &one,
            &Boolean::Is(self_is_identity.clone()),
        )?;

        let tmp_inv = tmp.inverse(&mut cs.namespace(|| "tmp_inv"))?;
        let tmp_inv = tmp_inv.reduce(&mut cs.namespace(|| "tmp_inv.reduce()"))?;

        let tmp_inv = PallasFp::conditionally_select(
            &mut cs.namespace(|| "is_inf ? 1 : tmp_inv"),
            &tmp_inv,
            &one,
            &Boolean::Is(self_is_identity.clone()),
        )?;

        // Now compute lambda as (G::Base::from(3) * self.x * self.x + G::GG::A()) * tmp_inv
        let x_squared = self.x.mul(&mut cs.namespace(|| "x_squared"), &self.x)?;
        let three = PallasFp::from(&BigInt::from(3))
            .allocate_field_element_unchecked(&mut cs.namespace(|| "three"))?;
        let prod_1 = x_squared.mul(&mut cs.namespace(|| "prod_1"), &three)?;

        let lambda_tmp = prod_1.add(&mut cs.namespace(|| "lambda_tmp"), A)?;
        let lambda = lambda_tmp.mul(&mut cs.namespace(|| "lambda"), &tmp_inv)?;

        /*************************************************************/
        //          x = lambda * lambda - self.x - self.x;
        /*************************************************************/
        let x_tmp = lambda.mul(&mut cs.namespace(|| "x_tmp_0"), &lambda)?;
        let x_tmp = x_tmp.sub(&mut cs.namespace(|| "x_tmp_1"), &self.x)?;
        let x = x_tmp.sub(&mut cs.namespace(|| "x"), &self.x)?;

        /*************************************************************/
        //        y = lambda * (self.x - x) - self.y;
        /*************************************************************/
        let x_minus_x = self.x.sub(&mut cs.namespace(|| "x_minus_x"), &x)?;
        let y_tmp = lambda.mul(&mut cs.namespace(|| "y_tmp"), &x_minus_x)?;
        let y = y_tmp.sub(&mut cs.namespace(|| "y"), &self.y)?;

        /*************************************************************/
        // Only return the computed x and y if the point is not infinity
        /*************************************************************/
        let zero =
            PallasFp::zero().allocate_field_element_unchecked(&mut cs.namespace(|| "zero"))?;
        // x
        let x = x.reduce(&mut cs.namespace(|| "x <- x.reduce()"))?;
        let x = PallasFp::conditionally_select(
            &mut cs.namespace(|| "final x"),
            &x,
            &zero.clone(),
            &Boolean::Is(self_is_identity.clone()),
        )?;

        // y
        let y = y.reduce(&mut cs.namespace(|| "y <- y.reduce()"))?;
        let y = PallasFp::conditionally_select(
            &mut cs.namespace(|| "final y"),
            &y,
            &zero,
            &Boolean::Is(self_is_identity),
        )?;

        Ok(AllocatedAffinePoint { x, y })
    }

    /// Double a point assuming it is not the point at infinity
    pub fn double_incomplete<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        A: &PallasFp<F>,
    ) -> Result<Self, SynthesisError> {
        //*************************************************************/
        // lambda = (G::Base::from(3) * self.x * self.x + G::GG::A())
        //  * (G::Base::from(2)) * self.y).invert().unwrap();
        /*************************************************************/

        // Compute tmp = (G::Base::ONE + G::Base::ONE)* self.y
        let tmp = self.y.add(&mut cs.namespace(|| "tmp_actual"), &self.y)?;

        // Now compute lambda as (G::Base::from(3) * self.x * self.x + G::GG::A()) * tmp_inv
        let x_squared = self.x.mul(&mut cs.namespace(|| "x_squared"), &self.x)?;
        let three = PallasFp::from(&BigInt::from(3))
            .allocate_field_element_unchecked(&mut cs.namespace(|| "three"))?;

        let prod_1 = x_squared.mul(&mut cs.namespace(|| "prod_1"), &three)?;

        let tmp_inv = tmp.inverse(&mut cs.namespace(|| "tmp_inv"))?;

        let lambda_tmp = prod_1.add(&mut cs.namespace(|| "lambda_tmp"), A)?;
        let lambda = lambda_tmp.mul(&mut cs.namespace(|| "lambda"), &tmp_inv)?;

        /*************************************************************/
        //          x = lambda * lambda - self.x - self.x;
        /*************************************************************/
        let x_tmp = lambda.mul(&mut cs.namespace(|| "x_tmp_0"), &lambda)?;
        let x_tmp = x_tmp.sub(&mut cs.namespace(|| "x_tmp_1"), &self.x)?;
        let x = x_tmp.sub(&mut cs.namespace(|| "x"), &self.x)?;

        /*************************************************************/
        //        y = lambda * (self.x - x) - self.y;
        /*************************************************************/
        let x_minus_x = self.x.sub(&mut cs.namespace(|| "x_minus_x"), &x)?;
        let y_tmp = lambda.mul(&mut cs.namespace(|| "y_tmp"), &x_minus_x)?;
        let y = y_tmp.sub(&mut cs.namespace(|| "y"), &self.y)?;

        Ok(AllocatedAffinePoint { x, y })
    }

    /// Add two points (may be equal)
    pub fn add<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        A: &PallasFp<F>,
    ) -> Result<Self, SynthesisError> {
        // Compute boolean equal indicating if self = other

        let equal_x = alloc_num_equals(
            cs.namespace(|| "check self.x == other.x"),
            &self.x,
            &other.x,
        )?;

        let equal_y = alloc_num_equals(
            cs.namespace(|| "check self.y == other.y"),
            &self.y,
            &other.y,
        )?;

        // Compute the result of the addition and the result of double self
        let result_from_add =
            self.add_internal(cs.namespace(|| "add internal"), other, &equal_x)?;
        let result_from_double = self.double(cs.namespace(|| "double"), A)?;

        // Output:
        // If (self == other) {
        //  return double(self)
        // }else {
        //  if (self.x == other.x){
        //      return infinity [negation]
        //  } else {
        //      return add(self, other)
        //  }
        // }
        let identity = Self::identity(cs.namespace(|| "identity"))?;
        let result_for_equal_x = Self::conditionally_select(
            cs.namespace(|| "equal_y ? result_from_double : infinity"),
            &result_from_double,
            &identity,
            &Boolean::from(equal_y),
        )?;

        Self::conditionally_select(
            cs.namespace(|| "equal ? result_from_double : result_from_add"),
            &result_for_equal_x,
            &result_from_add,
            &Boolean::from(equal_x),
        )
    }

    /// Adds other point to this point and returns the result. Assumes that the two points are
    /// different
    pub fn add_internal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        equal_x: &AllocatedBit,
    ) -> Result<Self, SynthesisError> {
        //*************************************************************/
        // lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
        /*************************************************************/

        // First compute (other.x - self.x).inverse()
        // If either self or other are the infinity point or self.x = other.x  then compute bogus values
        // Specifically,
        // x_diff = self != inf && other != inf && self.x == other.x ? (other.x - self.x) : 1
        let self_is_identity = self.alloc_is_identity(&mut cs.namespace(|| "self_is_identity"))?;
        let other_is_identity =
            other.alloc_is_identity(&mut cs.namespace(|| "other_is_identity"))?;
        let atleast_one_is_identity = Boolean::or(
            &mut cs.namespace(|| "atleast_one_is_identity"),
            &Boolean::Is(self_is_identity.clone()),
            &Boolean::Is(other_is_identity.clone()),
        )?;
        // Now compute x_diff_is_actual = at_least_one_inf OR equal_x
        let x_diff_is_actual = Boolean::or(
            &mut cs.namespace(|| "x_diff_is_actual"),
            &atleast_one_is_identity,
            &Boolean::Is(equal_x.clone()),
        )?;

        let one = PallasFp::one().allocate_field_element_unchecked(&mut cs.namespace(|| "one"))?;
        // x_diff = 1 if either self.is_infinity or other.is_infinity or self.x = other.x else self.x -
        // other.x

        // Compute tmp = (other.x - self.x) ? self != inf : 1
        let x_minus_x = other
            .x
            .sub(&mut cs.namespace(|| "other.x_minus_self.x"), &self.x)?;
        let x_minus_x = x_minus_x.reduce(&mut cs.namespace(|| "x_minus_x.reduce()"))?;
        let x_minus_x = PallasFp::conditionally_select(
            &mut cs.namespace(|| "x_diff_is_actual ? x_diff : 1"),
            &x_minus_x,
            &one,
            &x_diff_is_actual,
        )?;

        // Now compute lambda as (other.y - self.y) * other.x - self.x).invert()
        let y_minus_y = other.y.sub(&mut cs.namespace(|| "y_minus_y"), &self.y)?;

        let x_minus_x_inv = x_minus_x.inverse(&mut cs.namespace(|| "x_minus_x_inv"))?;
        let x_minus_x_inv = x_minus_x_inv.reduce(&mut cs.namespace(|| "x_minus_x_inv.reduce()"))?;

        let x_minus_x_inv = PallasFp::conditionally_select(
            &mut cs.namespace(|| "x_diff_is_actual ? 1 : x_diff_inv"),
            &x_minus_x_inv,
            &one,
            &x_diff_is_actual,
        )?;

        let lambda = y_minus_y.mul(&mut cs.namespace(|| "lambda"), &x_minus_x_inv)?;

        /*************************************************************/
        //          x = lambda * lambda - self.x - other.x;
        /*************************************************************/
        let x_tmp = lambda.mul(&mut cs.namespace(|| "x_tmp_0"), &lambda)?;
        let x_tmp = x_tmp.sub(&mut cs.namespace(|| "x_tmp_1"), &self.x)?;
        let x = x_tmp.sub(&mut cs.namespace(|| "x"), &other.x)?;

        /*************************************************************/
        //        y = lambda * (self.x - x) - self.y;
        /*************************************************************/
        let x_minus_x = self.x.sub(&mut cs.namespace(|| "self.x_minus_x"), &x)?;
        let y_tmp = lambda.mul(&mut cs.namespace(|| "y_tmp"), &x_minus_x)?;
        let y = y_tmp.sub(&mut cs.namespace(|| "y"), &self.y)?;

        //************************************************************************/
        // We only return the computed x, y if neither of the points is infinity and self.x != other.y
        // if self.is_infinity return other.clone()
        // elif other.is_infinity return self.clone()
        // elif self.x == other.x return infinity
        // Otherwise return the computed points.
        //************************************************************************/
        // Now compute the output x
        let x = x.reduce(&mut cs.namespace(|| "x <- x.reduce()"))?;
        let x1 = PallasFp::conditionally_select(
            &mut cs.namespace(|| "x1 = other.is_infinity ? self.x : x"),
            &x,
            &self.x,
            &Boolean::Is(other_is_identity.clone()),
        )?;

        let x = PallasFp::conditionally_select(
            &mut cs.namespace(|| "x = self.is_infinity ? other.x : x1"),
            &x1,
            &other.x,
            &Boolean::Is(self_is_identity.clone()),
        )?;

        // Now compute the output y
        let y = y.reduce(&mut cs.namespace(|| "y <- y.reduce()"))?;
        let y1 = PallasFp::conditionally_select(
            &mut cs.namespace(|| "y1 = other.is_infinity ? self.y : y"),
            &y,
            &self.y,
            &Boolean::Is(other_is_identity.clone()),
        )?;

        let y = PallasFp::conditionally_select(
            &mut cs.namespace(|| "y = self.is_infinity ? other.y : y1"),
            &y1,
            &other.y,
            &Boolean::Is(self_is_identity),
        )?;

        Ok(AllocatedAffinePoint { x, y })
    }

    /// Add two points assuming they are not the point at infinity and do not equal each other
    pub fn add_incomplete<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        //*************************************************************/
        // lambda = (other.y - self.y) * (other.x - self.x).invert().unwrap();
        /*************************************************************/

        // Compute tmp = (other.x - self.x) ? self != inf : 1
        let x_minus_x = other
            .x
            .sub(&mut cs.namespace(|| "other.x_minus_self.x"), &self.x)?;

        // Now compute lambda as (other.y - self.y) * other.x - self.x).invert()
        let y_minus_y = other.y.sub(&mut cs.namespace(|| "y_minus_y"), &self.y)?;

        let x_minus_x_inv = x_minus_x.inverse(&mut cs.namespace(|| "tmp_inv"))?;

        let lambda = y_minus_y.mul(&mut cs.namespace(|| "lambda"), &x_minus_x_inv)?;

        /*************************************************************/
        //          x = lambda * lambda - self.x - other.x;
        /*************************************************************/
        let x_tmp = lambda.mul(&mut cs.namespace(|| "x_tmp_0"), &lambda)?;
        let x_tmp = x_tmp.sub(&mut cs.namespace(|| "x_tmp_1"), &self.x)?;
        let x = x_tmp.sub(&mut cs.namespace(|| "x"), &other.x)?;

        /*************************************************************/
        //        y = lambda * (self.x - x) - self.y;
        /*************************************************************/
        let x_minus_x = self.x.sub(&mut cs.namespace(|| "self.x_minus_x"), &x)?;
        let y_tmp = lambda.mul(&mut cs.namespace(|| "y_tmp"), &x_minus_x)?;
        let y = y_tmp.sub(&mut cs.namespace(|| "y"), &self.y)?;

        Ok(AllocatedAffinePoint { x, y })
    }

    /// If condition outputs a otherwise outputs b
    pub fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let x = PallasFp::conditionally_select(
            &mut cs.namespace(|| "select x"),
            &b.x,
            &a.x,
            condition,
        )?;
        let y = PallasFp::conditionally_select(
            &mut cs.namespace(|| "select y"),
            &b.y,
            &a.y,
            condition,
        )?;

        Ok(Self { x, y })
    }

    /// A gadget for scalar multiplication, optimized to use incomplete addition law.
    /// The optimization here is analogous to <https://github.com/arkworks-rs/r1cs-std/blob/6d64f379a27011b3629cf4c9cb38b7b7b695d5a0/src/groups/curves/short_weierstrass/mod.rs#L295>,
    /// except we use complete addition law over affine coordinates instead of projective coordinates for the tail bits
    pub fn scalar_mul<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        scalar_bits: &[AllocatedBit],
        A: &PallasFp<F>,
        num_bits: u32,
    ) -> Result<Self, SynthesisError> {
        let split_len = core::cmp::min(scalar_bits.len(), (num_bits - 2) as usize);
        let (incomplete_bits, complete_bits) = scalar_bits.split_at(split_len);
        let mut p = self.clone();
        // we assume the first bit to be 1, so we must initialize acc to self and double it
        // we remove this assumption below
        let mut acc = p;
        p = acc.double_incomplete(cs.namespace(|| "double"), A)?;

        // perform the double-and-add loop to compute the scalar mul using incomplete addition law
        for (i, bit) in incomplete_bits.iter().enumerate().skip(1) {
            p = p.reduce(cs.namespace(|| format!("p_reduce_{i}")))?;
            let temp = acc.add_incomplete(cs.namespace(|| format!("add {i}")), &p)?;
            let temp = temp.reduce(cs.namespace(|| format!("reduce {i}")))?;

            acc = Self::conditionally_select(
                &mut cs.namespace(|| format!("acc_iteration_{i}")),
                &temp,
                &acc,
                &Boolean::from(bit.clone()),
            )?;

            p = p.double_incomplete(cs.namespace(|| format!("double {i}")), A)?;
        }

        // convert back to AllocatedPoint
        let res = {
            // we remove the initial slack if bits[0] is as not as assumed (i.e., it is not 1)
            let acc_minus_initial = {
                let neg = self.negate(cs.namespace(|| "negate"))?;
                acc.add(cs.namespace(|| "res minus self"), &neg, A)
            }?;

            Self::conditionally_select(
                cs.namespace(|| "remove slack if necessary"),
                &acc,
                &acc_minus_initial,
                &Boolean::from(scalar_bits[0].clone()),
            )?
        };

        // when self.is_infinity = 1, return the default point, else return res
        // we already set res.is_infinity to be self.is_infinity, so we do not need to set it here
        let self_is_identity = self.alloc_is_identity(&mut cs.namespace(|| "self_is_identity"))?;
        let default = Self::identity(cs.namespace(|| "default"))?;
        let mut acc = Self::conditionally_select(
            cs.namespace(|| "final incomplete bits result"),
            &default,
            &res,
            &Boolean::Is(self_is_identity),
        )?;

        for (i, bit) in complete_bits.iter().enumerate() {
            p = p.reduce(cs.namespace(|| format!("p_complete_reduce_{i}")))?;
            let temp = acc.add(cs.namespace(|| format!("add_complete {i}")), &p, A)?;
            let temp = temp.reduce(cs.namespace(|| format!("reduce_complete {i}")))?;
            acc = Self::conditionally_select(
                cs.namespace(|| format!("acc_complete_iteration_{i}")),
                &temp,
                &acc,
                &Boolean::from(bit.clone()),
            )?;

            p = p.double(cs.namespace(|| format!("double_complete {i}")), A)?;
        }

        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use crate::{alloc_num_equals, utils::f_to_nat, AllocatedAffinePoint, PallasFp};
    use bellpepper_core::{
        boolean::{AllocatedBit, Boolean},
        test_cs::TestConstraintSystem,
        ConstraintSystem, SynthesisError,
    };
    use pasta_curves::{
        arithmetic::{CurveAffine, CurveExt},
        group::{
            ff::{Field, PrimeField, PrimeFieldBits},
            Curve, Group,
        },
        pallas,
        pallas::Point,
        Fp, Fq,
    };
    use rand::{rngs::StdRng, SeedableRng};
    use std::ops::Add;

    pub fn scalar_mul(point: &pallas::Point, scalar: &Fq) -> pallas::Point {
        let mut res = pallas::Point::default();

        let bits = scalar.to_le_bits();
        for i in (0..bits.len()).rev() {
            res = res.double();
            if bits[i] {
                res = point.add(&res);
            }
        }
        res
    }

    #[test]
    fn test_non_circuit_scalar_mul() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);

        for _ in 0..100 {
            let point_a = Point::random(&mut rng);
            let scalar = Fq::random(&mut rng);

            let expected_mul = scalar_mul(&point_a, &scalar);
            let mul = point_a * scalar;

            assert_eq!(expected_mul, mul);
        }

        Ok(())
    }

    #[test]
    fn test_double() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let point_a = Point::random(&mut rng);

            let A = pallas::Point::a();

            let expected_double_a = point_a.double();
            let alloc_expected_double_a = AllocatedAffinePoint::alloc(
                cs.namespace(|| "expected_double_a"),
                &expected_double_a,
            )?;

            let alloc_point_a = AllocatedAffinePoint::alloc(cs.namespace(|| "a"), &point_a)?;
            let alloc_A = PallasFp::from(&f_to_nat(&A))
                .allocate_field_element_unchecked(&mut cs.namespace(|| "A"))?;

            let alloc_double_a = alloc_point_a.double(cs.namespace(|| "double_a"), &alloc_A)?;

            assert!(cs.is_satisfied());

            AllocatedAffinePoint::assert_equal(
                cs.namespace(|| "assert_equal"),
                &alloc_double_a,
                &alloc_expected_double_a,
            )?;
        }

        Ok(())
    }

    #[test]
    fn test_double_incomplete() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let point_a = Point::random(&mut rng);

            if point_a.to_affine().coordinates().is_none().unwrap_u8() == 1 {
                println!("point_a is not on the curve");
                continue;
            }

            let A = pallas::Point::a();

            let expected_double_a = point_a.double();
            let alloc_expected_double_a = AllocatedAffinePoint::alloc(
                cs.namespace(|| "expected_double_a"),
                &expected_double_a,
            )?;

            let alloc_point_a = AllocatedAffinePoint::alloc(cs.namespace(|| "a"), &point_a)?;
            let alloc_A = PallasFp::from(&f_to_nat(&A))
                .allocate_field_element_unchecked(&mut cs.namespace(|| "A"))?;

            let alloc_double_a =
                alloc_point_a.double_incomplete(cs.namespace(|| "double_a"), &alloc_A)?;

            assert!(cs.is_satisfied());

            AllocatedAffinePoint::assert_equal(
                cs.namespace(|| "assert_equal"),
                &alloc_double_a,
                &alloc_expected_double_a,
            )?;
        }

        Ok(())
    }

    #[test]
    fn test_add() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let point_a = Point::random(&mut rng);
            let point_b = Point::random(&mut rng);

            let expected_add = point_a.add(&point_b);
            let alloc_expected_add =
                AllocatedAffinePoint::alloc(cs.namespace(|| "expected_add"), &expected_add)?;

            let alloc_point_a = AllocatedAffinePoint::alloc(cs.namespace(|| "a"), &point_a)?;
            let alloc_point_b = AllocatedAffinePoint::alloc(cs.namespace(|| "b"), &point_b)?;

            let alloc_A = PallasFp::from(&f_to_nat(&Point::a()))
                .allocate_field_element_unchecked(&mut cs.namespace(|| "A"))?;

            let alloc_add = alloc_point_a.add(cs.namespace(|| "add"), &alloc_point_b, &alloc_A)?;

            assert!(cs.is_satisfied());

            AllocatedAffinePoint::assert_equal(
                cs.namespace(|| "assert_equal"),
                &alloc_add,
                &alloc_expected_add,
            )?;
        }

        Ok(())
    }

    #[test]
    fn test_add_incomplete() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let point_a = Point::random(&mut rng);
            let point_b = Point::random(&mut rng);

            if point_a.to_affine().coordinates().is_none().unwrap_u8() == 1
                || point_b.to_affine().coordinates().is_none().unwrap_u8() == 1
            {
                println!("point_a or point_b is not on the curve");
                continue;
            }

            let expected_add = point_a.add(&point_b);
            let alloc_expected_add =
                AllocatedAffinePoint::alloc(cs.namespace(|| "expected_add"), &expected_add)?;

            let alloc_point_a = AllocatedAffinePoint::alloc(cs.namespace(|| "a"), &point_a)?;
            let alloc_point_b = AllocatedAffinePoint::alloc(cs.namespace(|| "b"), &point_b)?;

            let alloc_add = alloc_point_a.add_incomplete(cs.namespace(|| "add"), &alloc_point_b)?;

            assert!(cs.is_satisfied());

            AllocatedAffinePoint::assert_equal(
                cs.namespace(|| "assert_equal"),
                &alloc_add,
                &alloc_expected_add,
            )?;
        }

        Ok(())
    }

    #[test]
    fn test_scalar_mul() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);

        for _ in 0..1 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let point_a = Point::random(&mut rng);
            let scalar = Fq::random(&mut rng);

            if point_a.to_affine().coordinates().is_none().unwrap_u8() == 1 {
                println!("point_a is not on the curve");
                continue;
            }

            let expected_mul = scalar_mul(&point_a, &scalar);
            let alloc_expected_mul =
                AllocatedAffinePoint::alloc(cs.namespace(|| "expected_mul"), &expected_mul)?;

            let alloc_point_a = AllocatedAffinePoint::alloc(cs.namespace(|| "a"), &point_a)?;
            let scalar_bits = scalar.to_le_bits();
            let alloc_scalar_bits = scalar_bits
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    AllocatedBit::alloc(cs.namespace(|| format!("scalar bit {}", i)), Some(*bit))
                        .unwrap()
                })
                .collect::<Vec<_>>();

            let alloc_A = PallasFp::from(&f_to_nat(&Point::a()))
                .allocate_field_element_unchecked(&mut cs.namespace(|| "A"))?;

            let alloc_mul = alloc_point_a.scalar_mul(
                cs.namespace(|| "scalar_mul"),
                &alloc_scalar_bits,
                &alloc_A,
                Fq::NUM_BITS,
            )?;

            assert!(cs.is_satisfied());

            AllocatedAffinePoint::assert_equal(
                cs.namespace(|| "assert_equal"),
                &alloc_mul,
                &alloc_expected_mul,
            )?;
            println!("{:?}", cs.num_constraints());
        }

        Ok(())
    }

    #[test]
    fn test_alloc_num_equals() -> Result<(), SynthesisError> {
        let mut rng = StdRng::seed_from_u64(100);
        for i in 0..1000 {
            let mut cs = TestConstraintSystem::<Fq>::new();
            let a = Fp::random(&mut rng);
            let a = PallasFp::from(&f_to_nat(&a));

            let b = if i % 2 == 0 {
                a.clone()
            } else {
                PallasFp::from(&f_to_nat(&Fp::random(&mut rng)))
            };

            let alloc_a = a.allocate_field_element_unchecked(&mut cs.namespace(|| "a"))?;
            let alloc_b = b.allocate_field_element_unchecked(&mut cs.namespace(|| "b"))?;

            let result = alloc_num_equals(&mut cs, &alloc_a, &alloc_b)?;

            assert!(cs.is_satisfied());
            assert_eq!(result.get_value().unwrap(), i % 2 == 0);
        }

        Ok(())
    }

    #[test]
    fn check_conditional_select() -> Result<(), SynthesisError> {
        let mut cs = TestConstraintSystem::<Fq>::new();
        let a = AllocatedAffinePoint::identity(cs.namespace(|| "a"))?;

        let tmp = a.y.add(&mut cs.namespace(|| "tmp"), &a.y)?;
        let one = PallasFp::one().allocate_field_element_unchecked(&mut cs.namespace(|| "one"))?;
        let is_identity = a.alloc_is_identity(&mut cs.namespace(|| "is_identity"))?;

        let tmp = PallasFp::conditionally_select(
            &mut cs.namespace(|| "is_ident ? tmp: 1"),
            &tmp,
            &one,
            &Boolean::Is(is_identity.clone()),
        )?;

        let bit = alloc_num_equals(cs.namespace(|| "a == b"), &one, &tmp)?;

        assert!(cs.is_satisfied());
        assert!(bit.get_value().unwrap());
        Ok(())
    }
}
