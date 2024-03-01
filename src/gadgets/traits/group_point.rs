use std::sync::Arc;

use crate::cs::traits::cs::ConstraintSystem;
use pairing::{ff::PrimeField, GenericCurveAffine};

use super::{non_native_field::traits::NonNativeField, SmallField};

/// A trait for elliptic curve points
pub trait EllipticGroupPoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Initializes a new non-infinite affine point with the specified coordinates
    fn new<CS>(cs: &mut CS, x: NF, y: NF) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Initializes the point at infinity. x and y are set to zero, and is_infinity is set to true.
    fn infinity<CS>(cs: &mut CS, params: &Arc<NF::Params>) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Returns the x-coordinate of the point
    fn x(&self) -> &NF;

    /// Returns the y-coordinate of the point
    fn y(&self) -> &NF;

    /// Find the opposite point -X of the current point X.
    fn negate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Doubles the point X to obtain 2X.
    fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Adds the point X to the point Y to obtain X+Y.
    fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Subtracts the point Y from the point X to obtain X-Y.
    fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>;

    /// Multiplies the point X by the scalar n to obtain nX.
    fn mul<CS>(&mut self, cs: &mut CS, other: &GC::Base) -> Self
    where
        CS: ConstraintSystem<F>;
}
