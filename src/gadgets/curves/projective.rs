/*! Package for implementing the SW projective coordinates operations, including:
 - Point addition
 - Point doubling
 - Point negation
 - Point subtraction

The code below is based on the following paper: https://eprint.iacr.org/2015/1060.pdf.
*/

use crate::cs::traits::cs::ConstraintSystem;

use super::{
    affine::ExtendedAffinePoint,
    boolean::Boolean,
    non_native_field::traits::NonNativeField,
    traits::{group_point::EllipticGroupPoint, selectable::Selectable},
    Derivative, SmallField,
};
use pairing::{
    ff::{Field, PrimeField},
    GenericCurveAffine,
};
use std::{marker::PhantomData, sync::Arc};

/// This is a struct for representing a point in the SW projective coordinates.
#[derive(Derivative)]
#[derivative(Copy, Clone, Clone, Debug)]
pub struct SWProjectivePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    x: NF,
    y: NF,
    z: NF,
    pub _marker: PhantomData<(F, GC)>,
}

impl<F, GC, NF> EllipticGroupPoint<F, GC, NF> for SWProjectivePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Initializes a new point in the SW projective coordinates with the specified coordinates.
    fn new<CS>(cs: &mut CS, x: NF, y: NF) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = x.get_params();
        let z = NF::allocated_constant(cs, GC::Base::one(), params);

        Self {
            x,
            y,
            z,
            _marker: PhantomData,
        }
    }

    /// Initializes the zero point of the curve, which is represented by a point `(0 : 1 : 0)`.
    fn infinity<CS>(cs: &mut CS, params: &Arc<NF::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self {
            x: NF::allocated_constant(cs, GC::Base::zero(), params),
            y: NF::allocated_constant(cs, GC::Base::one(), params),
            z: NF::allocated_constant(cs, GC::Base::zero(), params),
            _marker: PhantomData,
        }
    }

    /// Returns the x-coordinate of the point
    fn x(&self) -> &NF {
        &self.x
    }

    /// Returns the y-coordinate of the point
    fn y(&self) -> &NF {
        &self.y
    }

    /// Doubles the point in the SW projective coordinates, that is, finds the point `2 * self`.
    /// This is a more optimized version of the generic double function.
    /// If the `a` coefficient of the curve is non-zero, the generic double function is called.
    fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        if !GC::a_coeff().is_zero() {
            return self.generic_double(cs);
        }

        self.invariant_0_exception_free_doubling(cs)
    }

    /// Negates the point in the SW projective coordinates.
    /// The negation of the point `(x : y : z)` is `(x : -y : z)`.
    fn negate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self {
            x: self.x.clone(),
            y: self.y.negated(cs),
            z: self.z.clone(),
            _marker: PhantomData,
        }
    }

    /// Multiplies the point in the SW projective coordinates by a scalar.
    fn mul<CS>(&mut self, cs: &mut CS, scalar: &GC::Base) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // For now we mock the double and add algorithm which is not optimal
        return self.mul_scalar_double_and_add(cs, &scalar);
    }

    /// Add the point in affine coordinates to the point in the projective coordinates.
    fn add<CS>(&mut self, cs: &mut CS, other_xy: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.add_sub_mixed_impl(cs, other_xy, false)
    }

    /// Subtracts a point in the affine coordinates from the point in the projective coordinates.
    fn sub<CS>(&mut self, cs: &mut CS, other_xy: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.add_sub_mixed_impl(cs, other_xy, true)
    }
}

impl<F, GC, NF> SWProjectivePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Initializes a new point in the SW projective coordinates with the specified coordinates.
    pub fn from_affine<CS>(cs: &mut CS, affine_point: ExtendedAffinePoint<F, GC, NF>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self::new(cs, affine_point.x().clone(), affine_point.y().clone())
    }

    /// Doubles the point in the SW projective coordinates, that is, finds the point `2 * self`.
    /// This is a more optimized version of the generic double function, using
    /// exception-free doubling.
    fn invariant_0_exception_free_doubling<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Initialize constants three and four
        let mut two_scalar = GC::Base::one();
        two_scalar.double();

        let mut three_scalar = GC::Base::one();
        three_scalar.add_assign(&two_scalar);

        let mut four_scalar = two_scalar.clone();
        four_scalar.double();

        // Extracting b parameter in Weisstrass equation, and calculating 3b
        let curve_b = GC::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        // Getting 3 and 4 in non-native field, and initializing curve_b3 in non-native field
        let params = self.x.get_params().clone();
        let mut three_nf = NF::allocated_constant(cs, three_scalar, &params);
        let mut four_nf = NF::allocated_constant(cs, four_scalar, &params);
        let mut curve_b3_nf = NF::allocated_constant(cs, curve_b3, &params);

        // Preparing helper variables
        let x = &mut self.x;
        let y = &mut self.y;
        let z = &mut self.z;

        // t0 = y * y
        let mut t0 = y.square(cs);
        // t2 = b3 * z * z
        let mut b3_mul_z = z.mul(cs, &mut curve_b3_nf);
        let mut t2 = b3_mul_z.mul(cs, z);
        // y3 = t0 + t2
        let mut y3: NF = t0.add(cs, &mut t2);
        // t1 = y * z
        let mut t1 = y.mul(cs, z);
        // z3 = 8 * t0 * t1
        let mut t0_mul_4 = t0.mul(cs, &mut four_nf);
        let mut t0_mul_8 = t0_mul_4.double(cs);
        let z3 = t0_mul_8.mul(cs, &mut t1);
        // t4 = 4 * t0 - 3 * y3
        let mut y3_mul_3 = y3.mul(cs, &mut three_nf);
        let mut t4 = t0_mul_4.sub(cs, &mut y3_mul_3);
        // y3 = t4 * y3
        let mut y3 = t4.mul(cs, &mut y3);
        // y3 = 8 * t0 * t2 + y3
        let mut new_y3 = t0_mul_8.mul(cs, &mut t2);
        let new_y3 = new_y3.add(cs, &mut y3);
        let y3 = new_y3;
        // t1 = x * y
        let mut t1 = x.mul(cs, y);
        // x3 = 2 * t4 * t1
        let mut t4_mul_2 = t4.double(cs);
        let x3 = t4_mul_2.mul(cs, &mut t1);

        Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: PhantomData,
        }
    }

    /// Doubling the point generically, which is a bit slower compared to the optimized version.
    /// This function is called when the `a` coefficient of the curve is non-zero.
    fn generic_double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Calculating 3*b
        let b = GC::b_coeff();
        let mut b_tripled = b;
        b_tripled.double();
        b_tripled.add_assign(&b);

        // Making a and b in non-native field
        let params = self.x.get_params().clone();
        let mut a = NF::allocated_constant(cs, GC::a_coeff(), &params);
        let mut b_tripled = NF::allocated_constant(cs, b_tripled, &params);

        // Preparing helper variables
        let x = &mut self.x;
        let y = &mut self.y;
        let z = &mut self.z;

        // t0 = x * x
        let mut t0 = x.square(cs);
        // t1 = y * y
        let mut t1 = y.square(cs);
        // t2 = z * z
        let mut t2 = z.square(cs);

        // t3 = x * y
        let mut t3 = x.mul(cs, y);
        // t3 = t3 + t3
        let mut t3 = t3.double(cs);
        // z3 = x * z
        let mut z3 = x.mul(cs, z);

        // z3 = z3 + z3
        let mut z3 = z3.double(cs);
        // x3 = a * z3
        let mut x3 = a.mul(cs, &mut z3);
        // y3 = b3 * t2
        let mut y3 = b_tripled.mul(cs, &mut t2);

        // y3 = x3 + y3
        let mut y3 = x3.add(cs, &mut y3);
        // x3 = t1 - y3
        let mut x3 = t1.sub(cs, &mut y3);
        // y3 = t1 + y3
        let mut y3 = t1.add(cs, &mut y3);

        // y3 = x3 * y3
        let mut y3 = x3.mul(cs, &mut y3);
        // x3 = t3 * x3
        let mut x3 = t3.mul(cs, &mut x3);
        // z3 = b3 * z3
        let mut z3 = b_tripled.mul(cs, &mut z3);

        // t2 = a * t2
        let mut t2 = a.mul(cs, &mut t2);
        // t3 = t0 - t2
        let mut t3 = t0.sub(cs, &mut t2);
        // t3 = a * t3
        let mut t3 = a.mul(cs, &mut t3);

        // t3 = t3 + z3
        let mut t3 = t3.add(cs, &mut z3);
        // z3 = t0 + t0
        let mut z3 = t0.double(cs);
        // t0 = z3 + t0
        let mut t0 = z3.add(cs, &mut t0);

        // t0 = t0 + t2
        let mut t0 = t0.add(cs, &mut t2);
        // t0 = t0 * t3
        let mut t0 = t0.mul(cs, &mut t3);
        // y3 = y3 + y0
        let y3 = y3.add(cs, &mut t0);

        // t2 = y * z
        let mut t2 = y.mul(cs, z);
        // t2 = t2 + t2
        let mut t2 = t2.double(cs);
        // t0 = t2 * t3
        let mut t0 = t2.mul(cs, &mut t3);

        // x3 = x3 - t0
        let x3 = x3.sub(cs, &mut t0);
        // z3 = t2 * t1
        let mut z3 = t2.mul(cs, &mut t1);
        // z3 = z3 + z3
        let mut z3 = z3.double(cs);

        // z3 = z3 + z3
        let z3 = z3.double(cs);

        self.x = x3.clone();
        self.y = y3.clone();
        self.z = z3.clone();
        Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: PhantomData,
        }
    }

    /// Multiplies the point in the SW projective coordinates by a scalar using the double-and-add algorithm.
    /// See https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#Double-and-add
    fn mul_scalar_double_and_add<CS>(&mut self, cs: &mut CS, scalar: &GC::Base) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut result = Self::infinity(cs, self.x.get_params());
        let mut temp = self.clone();


        // Convert the scalar to bits
        let scalar_bits = scalar
            .into_repr()
            .as_ref()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| (byte >> i) & 1 == 1))
            .collect::<Vec<_>>();

        for bit in scalar_bits {
            if bit {
                result = result.add(cs, &mut temp);
            }
            temp.double(cs);
        }

        result
    }

    /// Mixed addition/subtraction of the point in the SW projective coordinates with
    /// another SW projective-represented point.
    fn add_sub_mixed_impl<CS>(&mut self, cs: &mut CS, other: &mut Self, subtraction: bool) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        if GC::a_coeff().is_zero() == false {
            return self.generic_add_sub_mixed_impl(cs, other, subtraction);
        }

        let params = self.x.get_params().clone();

        let mut three = GC::Base::one();
        three.double();
        three.add_assign(&GC::Base::one());

        let curve_b = GC::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut curve_b6 = curve_b3;
        curve_b6.double();

        let mut three_nn = NF::allocated_constant(cs, three, &params);
        let mut curve_b3 = NF::allocated_constant(cs, curve_b3, &params);
        let mut curve_b6 = NF::allocated_constant(cs, curve_b6, &params);

        let x1 = &mut self.x;
        let y1 = &mut self.y;
        let z1 = &mut self.z;

        let mut y2_local: NF = other.y.clone();
        let x2 = &mut other.x;
        if subtraction {
            y2_local = y2_local.negated(cs);
        }
        let y2 = &mut y2_local;

        // t4 = y2 * z1 + y1
        let mut t4 = y2.mul(cs, z1);
        let mut t4 = t4.add(cs, y1);

        // y3 = x2 * z1 + x1
        let mut y3 = x2.mul(cs, z1);
        let mut y3 = y3.add(cs, x1);

        // z3 = y1 * y2 + b3 * z1
        let mut z1_mul_b3 = z1.mul(cs, &mut curve_b3);
        let mut z3 = y1.mul(cs, y2);
        let mut z3 = z3.add(cs, &mut z1_mul_b3);

        // t0 = x1 * x2
        let mut t0 = x1.mul(cs, x2);

        // t3 = (x2 + y2) * (x1 + y1) - t0 - z3 + b3 * z1
        let mut a = x2.add(cs, y2);
        let mut b = x1.add(cs, y1);
        let mut t3 = a.mul(cs, &mut b);
        let mut t3 = t3.sub(cs, &mut t0);
        let mut t3 = t3.sub(cs, &mut z3);
        let mut t3 = t3.add(cs, &mut z1_mul_b3);

        // x3 = t4 * b3 * y3
        let mut y3_mul_b3 = y3.mul(cs, &mut curve_b3);
        let mut x3 = t4.mul(cs, &mut y3_mul_b3);

        // t1 = z3 - 2 * b3 * z1
        let mut z1_mul_2_b3 = z1.mul(cs, &mut curve_b6);
        let mut t1 = z3.sub(cs, &mut z1_mul_2_b3);

        // x3 = t3 * t1 - x3
        let mut new_x3 = t3.mul(cs, &mut t1);
        let new_x3 = new_x3.sub(cs, &mut x3);
        let x3 = new_x3;

        // y3 = (b3 * y3) * (3 * t0)
        let mut t0_mul_3 = t0.mul(cs, &mut three_nn);
        let mut y3 = y3_mul_b3.mul(cs, &mut t0_mul_3);

        // y3 = t1 * z3  + y3
        let mut new_y3 = t1.mul(cs, &mut z3);
        let new_y3 = new_y3.add(cs, &mut y3);
        let y3 = new_y3;

        // t0 = (3 * t0) * t3
        let mut t0 = t0_mul_3.mul(cs, &mut t3);

        // z3 = z3 * t4 + t0
        let mut z3 = z3.mul(cs, &mut t4);
        let z3 = z3.add(cs, &mut t0);

        Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: PhantomData,
        }
    }

    /// Adds (subtracts) another point in the affine coordinates generically.
    /// To specify add/sub operation, the `is_subtraction` parameter is used.
    fn generic_add_sub_mixed_impl<CS>(
        &mut self,
        cs: &mut CS,
        point: &mut Self,
        subtraction: bool,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.x.get_params().clone();

        let curve_b = GC::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut curve_a = NF::allocated_constant(cs, GC::a_coeff(), &params);
        let mut curve_b3 = NF::allocated_constant(cs, curve_b3, &params);

        let x1 = &mut self.x;
        let y1 = &mut self.y;
        let z1 = &mut self.z;

        let mut y2_local: NF = point.y.clone();
        let x2 = &mut point.x;
        if subtraction {
            y2_local = y2_local.negated(cs);
        }
        let y2 = &mut y2_local;

        // t0 = x1 * x2
        let mut t0 = x1.mul(cs, x2);
        // t1 = x1 * y2
        let mut t1 = y1.mul(cs, y2);
        // t3 = x2 + y2
        let mut t3 = x2.add(cs, y2);

        // t4 = x1 + y1
        let mut t4 = x1.add(cs, y1);
        // t3 = t3 * t4
        let mut t3 = t3.mul(cs, &mut t4);
        // t4 = t0 + t1
        let mut t4 = t0.add(cs, &mut t1);

        // t3 = t3 - t4
        let mut t3 = t3.sub(cs, &mut t4);
        // t4 = x2 * z1
        let mut t4 = x2.mul(cs, z1);
        // t4 = t4 + x1
        let mut t4 = t4.add(cs, x1);

        // t5 = y2 * z1
        let mut t5 = y2.mul(cs, z1);
        // t5 = t5 + y1
        let mut t5 = t5.add(cs, y1);
        // z3 = a * t4
        let mut z3 = curve_a.mul(cs, &mut t4);

        // x3 = b3 * z1
        let mut x3 = curve_b3.mul(cs, z1);
        // z3 = x3 + z3
        let mut z3 = x3.add(cs, &mut z3);
        // x3 = t1 - z3
        let mut x3 = t1.sub(cs, &mut z3);

        // z3 = t1 + z3
        let mut z3 = t1.add(cs, &mut z3);
        // y3 = x3 * z3
        let mut y3 = x3.mul(cs, &mut z3);
        // t1 = t0 + t0
        let mut t1 = t0.double(cs);

        // t1 = t1 + t0
        let mut t1 = t1.add(cs, &mut t0);
        // t2 = a * z1
        let mut t2 = curve_a.mul(cs, z1);
        // t4 = b3 * t4
        let mut t4 = curve_b3.mul(cs, &mut t4);

        // t1 = t1 + t2
        let mut t1 = t1.add(cs, &mut t2);
        // t2 = t0 - t2
        let mut t2 = t0.sub(cs, &mut t2);
        // t2 = a * t2
        let mut t2 = curve_a.mul(cs, &mut t2);

        // t4 = t4 + t2
        let mut t4 = t4.add(cs, &mut t2);
        // t0 = t1 * t4
        let mut t0 = t1.mul(cs, &mut t4);
        // y3 = y3 + t0
        let y3 = y3.add(cs, &mut t0);

        // t0 = t5 * t4
        let mut t0 = t5.mul(cs, &mut t4);
        // x3 = t3 * x3
        let mut x3 = t3.mul(cs, &mut x3);
        // x3 = x3 - t0
        let x3 = x3.sub(cs, &mut t0);

        // t0 = t3 * t1
        let mut t0 = t3.mul(cs, &mut t1);
        // z3 = t5 * z3
        let mut z3 = t5.mul(cs, &mut z3);
        // z3 = z3 + t0
        let z3 = z3.add(cs, &mut t0);

        Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: PhantomData,
        }
    }

    /// Converts the point back to the affine coordinates.
    pub fn to_affine<CS>(&mut self, cs: &mut CS) -> ExtendedAffinePoint<F, GC, NF>
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.x.get_params().clone();

        // Handle the case where self.z is zero (i.e., the point is at infinity)
        let at_infinity = NF::is_zero(&mut self.z, cs);
        let boolean_true = Boolean::allocated_constant(cs, true);
        if at_infinity == boolean_true {
            return ExtendedAffinePoint::infinity(cs, &params);
        }

        // Return the point in the affine coordinates (X/Z, Y/Z)
        // Since we checked that Z is not zero, we can safely divide by Z
        let x = self.x.div_unchecked(cs, &mut self.z);
        let y = self.y.div_unchecked(cs, &mut self.z);

        ExtendedAffinePoint::new(cs, x, y)
    }
}

impl<F, GC, NF> Selectable<F> for SWProjectivePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Given constraint system `cs`, a boolean `flag`, and two points `a` and `b`, this function
    /// returns a point that is equal to `a` if `flag` is true, and equal to `b` otherwise.
    fn conditionally_select<CS>(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let x = NF::conditionally_select(cs, flag, &a.x, &b.x);
        let y = NF::conditionally_select(cs, flag, &a.y, &b.y);
        let z = NF::conditionally_select(cs, flag, &a.z, &b.z);

        Self {
            x,
            y,
            z,
            _marker: PhantomData,
        }
    }
}
