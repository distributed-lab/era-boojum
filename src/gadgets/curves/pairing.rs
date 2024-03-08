/*!
    This module contains the EC pairing implementation using Ate pairing (classic Miller loop).
    See paper https://eprint.iacr.org/2019/077.pdf for more details.
*/

use pairing::{ff::Field, GenericCurveAffine};

use crate::cs::traits::cs::ConstraintSystem;

use super::SmallField;

pub trait ECPairable<F, G1, G2, GT, const U: u64>
where
    F: SmallField,
    G1: GenericCurveAffine,
    G2: GenericCurveAffine,
    GT: Field,
{
    fn pairing<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        point_1: &mut G1,
        point_2: &mut G2,
    ) -> GT;
}

pub struct ECPairing<F, G1, G2, GT, const U: u64> 
where 
    F: SmallField,
    G1: GenericCurveAffine,
    G2: GenericCurveAffine,
    GT: Field,
{
    _marker: std::marker::PhantomData<(F, G1, G2, GT)>,
}

impl<F, G1, G2, GT> ECPairable<F, G1, G2, GT, 64> for ECPairing<F, G1, G2, GT, 64>
where
    F: SmallField,
    G1: GenericCurveAffine,
    G2: GenericCurveAffine,
    GT: Field,
{
    fn pairing<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        _p: &mut G1,
        q: &mut G2,
    ) -> GT {
        let f = GT::one();
        let _t = q;
        f
    }
}