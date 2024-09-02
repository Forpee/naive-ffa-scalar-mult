use bellpepper_core::{test_cs::TestConstraintSystem, ConstraintSystem};
use bellpepper_emulated::field_element::{EmulatedFieldElement, EmulatedFieldParams};
use num_bigint::{BigInt, RandBigInt};
use num_traits::{identities::Zero, One};
use pasta_curves::Fq;
use std::ops::Rem;

use crate::PallasFpParams;

#[test]
fn test_constant_equality() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let a_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());

    let a_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a_int);

    let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
    assert!(a.is_ok());
    let a = a.unwrap();

    let res = a.assert_equality_to_constant(&mut cs.namespace(|| "check equality"), &a_const);
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 5);
}

#[test]
fn test_alloc_is_zero() {
    let mut cs = TestConstraintSystem::<Fq>::new();

    let one_const = EmulatedFieldElement::<Fq, PallasFpParams>::one();
    let one_alloc = one_const.allocate_field_element_unchecked(&mut cs.namespace(|| "one"));
    assert!(one_alloc.is_ok());
    let one = one_alloc.unwrap();

    let res = one.alloc_is_zero(&mut cs.namespace(|| "check if one == zero"));
    assert!(res.is_ok());
    let one_is_zero = res.unwrap();
    assert!(!one_is_zero.get_value().unwrap());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 19);

    let zero_const = EmulatedFieldElement::<Fq, PallasFpParams>::zero();
    let zero_alloc = zero_const.allocate_field_element_unchecked(&mut cs.namespace(|| "zero"));
    assert!(zero_alloc.is_ok());
    let zero = zero_alloc.unwrap();

    let res = zero.alloc_is_zero(&mut cs.namespace(|| "check if zero == zero"));
    assert!(res.is_ok());
    let zero_is_zero = res.unwrap();
    assert!(zero_is_zero.get_value().unwrap());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 38);
}

#[test]
fn test_add() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let a_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let b_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let sum_int = (&a_int + &b_int).rem(&PallasFpParams::modulus());

    let a_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a_int);
    let b_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&b_int);
    let sum_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&sum_int);

    let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
    let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
    let sum = sum_const.allocate_field_element_unchecked(&mut cs.namespace(|| "sum"));
    assert!(a.is_ok());
    assert!(b.is_ok());
    assert!(sum.is_ok());
    let a = a.unwrap();
    let b = b.unwrap();
    let sum = sum.unwrap();

    let sum_calc = a.add(&mut cs.namespace(|| "a + b"), &b);
    assert!(sum_calc.is_ok());
    let sum_calc = sum_calc.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality"),
        &sum_calc,
        &sum,
    );
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 158);
}

#[test]
fn test_sub() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let tmp1 = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let tmp2 = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let a_int = (&tmp1).max(&tmp2);
    let b_int = (&tmp1).min(&tmp2);
    let diff_int = (a_int - b_int).rem(&PallasFpParams::modulus());

    let a_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(a_int);
    let b_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(b_int);
    let diff_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&diff_int);

    let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
    let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
    let diff = diff_const.allocate_field_element_unchecked(&mut cs.namespace(|| "diff"));
    assert!(a.is_ok());
    assert!(b.is_ok());
    assert!(diff.is_ok());
    let a = a.unwrap();
    let b = b.unwrap();
    let diff = diff.unwrap();

    let diff_calc = a.sub(&mut cs.namespace(|| "a - b"), &b);
    assert!(diff_calc.is_ok());
    let diff_calc = diff_calc.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality"),
        &diff_calc,
        &diff,
    );
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 158);
}

#[test]
fn test_mul() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let a_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let b_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let prod_int = (&a_int * &b_int).rem(&PallasFpParams::modulus());

    let a_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a_int);
    let b_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&b_int);
    let prod_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&prod_int);

    let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
    let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
    let prod = prod_const.allocate_field_element_unchecked(&mut cs.namespace(|| "prod"));
    assert!(a.is_ok());
    assert!(b.is_ok());
    assert!(prod.is_ok());
    let a = a.unwrap();
    let b = b.unwrap();
    let prod = prod.unwrap();

    let prod_calc = a.mul(&mut cs.namespace(|| "a * b"), &b);
    assert!(prod_calc.is_ok());
    let prod_calc = prod_calc.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality"),
        &prod_calc,
        &prod,
    );
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

#[test]
fn test_divide() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let a_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
    let b_int = rng.gen_bigint_range(&BigInt::one(), &PallasFpParams::modulus());
    let p = PallasFpParams::modulus();
    let p_minus_2 = &p - BigInt::from(2);
    // b^(p-1) = 1 mod p for non-zero b. So b^(-1) = b^(p-2)
    let b_inv_int = b_int.modpow(&p_minus_2, &p);
    let ratio_int = (&a_int * b_inv_int).rem(&p);

    let a_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a_int);
    let b_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&b_int);
    let ratio_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&ratio_int);

    let a = a_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
    let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
    let ratio = ratio_const.allocate_field_element_unchecked(&mut cs.namespace(|| "ratio"));
    assert!(a.is_ok());
    assert!(b.is_ok());
    assert!(ratio.is_ok());
    let a = a.unwrap();
    let b = b.unwrap();
    let ratio = ratio.unwrap();

    let ratio_calc = a.divide(&mut cs.namespace(|| "a divided by b"), &b);
    assert!(ratio_calc.is_ok());
    let ratio_calc = ratio_calc.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality"),
        &ratio_calc,
        &ratio,
    );
    assert!(res.is_ok());

    let b_mul_ratio = b.mul(&mut cs.namespace(|| "b * (a div b)"), &ratio);
    assert!(b_mul_ratio.is_ok());
    let b_mul_ratio = b_mul_ratio.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality of a and b * (a div b)"),
        &b_mul_ratio,
        &a,
    );
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

#[test]
fn test_inverse() {
    let mut cs = TestConstraintSystem::<Fq>::new();
    let mut rng = rand::thread_rng();
    let b_int = rng.gen_bigint_range(&BigInt::one(), &PallasFpParams::modulus());
    let p = PallasFpParams::modulus();
    let p_minus_2 = &p - BigInt::from(2);
    // b^(p-1) = 1 mod p for non-zero b. So b^(-1) = b^(p-2)
    let b_inv_int = b_int.modpow(&p_minus_2, &p);

    let b_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&b_int);
    let b_inv_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&b_inv_int);

    let b = b_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
    let b_inv = b_inv_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b_inv"));
    assert!(b.is_ok());
    assert!(b_inv.is_ok());
    let b = b.unwrap();
    let b_inv = b_inv.unwrap();

    let b_inv_calc = b.inverse(&mut cs.namespace(|| "b inverse"));
    assert!(b_inv_calc.is_ok());
    let b_inv_calc = b_inv_calc.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality"),
        &b_inv_calc,
        &b_inv,
    );
    assert!(res.is_ok());

    let b_mul_b_inv = b.mul(&mut cs.namespace(|| "b * b_inv"), &b_inv);
    assert!(b_mul_b_inv.is_ok());
    let b_mul_b_inv = b_mul_b_inv.unwrap();

    let res = EmulatedFieldElement::<Fq, PallasFpParams>::assert_is_equal(
        &mut cs.namespace(|| "check equality one and b * b_inv"),
        &b_mul_b_inv,
        &EmulatedFieldElement::<Fq, PallasFpParams>::one(),
    );
    assert!(res.is_ok());

    if !cs.is_satisfied() {
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());
}

// #[test]
// fn test_conditionally_select() {
//     let mut cs = TestConstraintSystem::<Fq>::new();
//     let mut rng = rand::thread_rng();
//     let a0_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());
//     let a1_int = rng.gen_bigint_range(&BigInt::zero(), &PallasFpParams::modulus());

//     let a0_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a0_int);
//     let a1_const = EmulatedFieldElement::<Fq, PallasFpParams>::from(&a1_int);

//     let one = TestConstraintSystem::<Fq>::one();
//     let conditions = vec![false, true];
//     for c in conditions.clone() {
//         let condition = Boolean::constant(c);

//         let res = EmulatedFieldElement::<Fq, PallasFpParams>::conditionally_select(
//             &mut cs.namespace(|| {
//                 format!("conditionally select constant a0 or a1 for condition = {c}")
//             }),
//             &a0_const,
//             &a1_const,
//             &condition,
//         );
//         assert!(res.is_ok());
//         if !c {
//             assert_eq!(cs.num_constraints(), 5);
//         }
//         let res = res.unwrap();

//         let res_expected_limbs = match (&a0_const.limbs, &a1_const.limbs) {
//             (EmulatedLimbs::Constant(a0_const_limbs), EmulatedLimbs::Constant(a1_const_limbs)) => {
//                 if c {
//                     a1_const_limbs
//                 } else {
//                     a0_const_limbs
//                 }
//             }
//             _ => panic!("Both sets of limbs must be constant"),
//         };

//         if let EmulatedLimbs::Allocated(res_limbs) = res.limbs {
//             for i in 0..res_limbs.len() {
//                 cs.enforce(
//                     || format!("c constant limb {i} equality for condition = {c}"),
//                     |lc| lc + &res_limbs[i].lc(Fq::one()),
//                     |lc| lc + one,
//                     |lc| lc + (res_expected_limbs[i], one),
//                 );
//             }
//         } else {
//             // Execution should not reach this line
//             eprintln!("res should have allocated limbs");
//             unreachable!();
//         }

//         if !cs.is_satisfied() {
//             eprintln!("{:?}", cs.which_is_unsatisfied());
//         }
//         assert!(cs.is_satisfied());
//     }
//     let num_constraints_here = cs.num_constraints();

//     let a0 = a0_const.allocate_field_element_unchecked(&mut cs.namespace(|| "a"));
//     let a1 = a1_const.allocate_field_element_unchecked(&mut cs.namespace(|| "b"));
//     assert!(a0.is_ok());
//     assert!(a1.is_ok());
//     let a0 = a0.unwrap();
//     let a1 = a1.unwrap();

//     for c in conditions {
//         let condition = Boolean::constant(c);

//         let res = EmulatedFieldElement::<Fq, PallasFpParams>::conditionally_select(
//             &mut cs
//                 .namespace(|| format!("conditionally select variable a or b for condition = {c}")),
//             &a0,
//             &a1,
//             &condition,
//         );
//         assert!(res.is_ok());
//         if !c {
//             assert_eq!(cs.num_constraints() - num_constraints_here, 5);
//         }
//         let res = res.unwrap();

//         let res_expected_limbs = match (&a0.limbs, &a1.limbs) {
//             (EmulatedLimbs::Allocated(a0_limbs), EmulatedLimbs::Allocated(a1_limbs)) => {
//                 if c {
//                     a1_limbs
//                 } else {
//                     a0_limbs
//                 }
//             }
//             _ => panic!("Both sets of limbs must be allocated"),
//         };

//         if let EmulatedLimbs::Allocated(res_limbs) = res.limbs {
//             for i in 0..res_limbs.len() {
//                 cs.enforce(
//                     || format!("c variable limb {i} equality for condition = {c}"),
//                     |lc| lc + &res_limbs[i].lc(Fq::one()),
//                     |lc| lc + one,
//                     |lc| lc + &res_expected_limbs[i].lc(Fq::one()),
//                 );
//             }
//         } else {
//             // Execution should not reach this line
//             eprintln!("res should have allocated limbs");
//             unreachable!();
//         }

//         if !cs.is_satisfied() {
//             eprintln!("{:?}", cs.which_is_unsatisfied());
//         }
//         assert!(cs.is_satisfied());
//     }
// }
