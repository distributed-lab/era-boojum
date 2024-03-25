use std::sync::Arc;

use pairing::ff::PrimeField;

use crate::{cs::traits::cs::ConstraintSystem, gadgets::curves::SmallField};

use super::*;

// The twist coefficient for the BN256 curve
const B_TWIST_COEFF_REAL: &str =
    "19485874751759354771024239261021720505790618469301721065564631296452457478373";
const B_TWIST_COEFF_IMAGINARY: &str =
    "266929791119991161246907387137283842545076965332900288569378510910307636690";

// Curve parameter for the BN256 curve
const CURVE_PARAMETER: &str = "4965661367192848881";
const CURVE_PARAMETER_WNAF: [i8; 63] = [
    1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0,
    0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0,
    0, 1,
];

/// Struct for the line function evaluation for the BN256 curve.
/// The line function is used in the Miller loop of the pairing function.
/// Implementation is primarily based on paper https://eprint.iacr.org/2019/077.pdf,
/// section 3: line functions.
pub struct LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    c0: BN256Fp2NNField<F>,
    c1: BN256Fp2NNField<F>,
    c2: BN256Fp2NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub fn new(cs: &mut CS, params: &Arc<BN256BaseNNFieldParams>) -> Self {
        Self {
            c0: BN256Fp2NNField::zero(cs, params),
            c1: BN256Fp2NNField::zero(cs, params),
            c2: BN256Fp2NNField::zero(cs, params),
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `l_{P,Q}(R)` when `P` and `Q` are distinct points on the twisted curve
    /// `E'(F_{p^2})` and `R` is a point on the regular curve `E(F_p)`.
    #[allow(non_snake_case)]
    pub fn at_line(
        mut self,
        cs: &mut CS,
        point1: &BN256Fp2ProjectiveCurvePoint<F>,
        point2: &BN256Fp2ProjectiveCurvePoint<F>,
        at: &mut SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>,
    ) -> Self {
        let mut X2 = &point1[0];
        let mut Y2 = &point1[1];
        let mut Z2 = &point2[2];

        let mut X = &point2[0];
        let mut Y = &point2[1];
        let mut Z = &point2[2];

        // c0 <- (X - Z * X2) * y_P
        let mut z_x2 = X2.mul(cs, &mut Z);
        let mut x_sub_z_x2 = X.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_c0(cs, &mut at.y);

        // c1 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = Z.mul(cs, &mut Y2);
        let mut y_sub_z_y2 = Y.sub(cs, &mut z_y2);
        let mut c1 = X2.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = Y2.mul(cs, &mut x_sub_z_x2);
        let c1 = c1.sub(cs, &mut y2_x_sub_z_x2);

        // c2 <- -(Y - Z * Y2) * x_P
        let mut c2 = y_sub_z_y2.negated(cs);
        let c2 = c2.mul_c0(cs, &mut at.x);

        self.c0 = c0;
        self.c1 = c1;
        self.c2 = c2;
        self
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `l_{P,P}(R)` when `P` is a point on the twisted curve `E'(F_{p^2})` and
    /// `R` is a point on the regular curve `E(F_p)`.
    #[allow(non_snake_case)]
    pub fn at_tangent(
        mut self,
        cs: &mut CS,
        p: &BN256Fp2ProjectiveCurvePoint<F>,
        point: &BN256Fp2ProjectiveCurvePoint<F>,
        at: &mut SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>,
    ) -> Self {
        let mut X = &point[0];
        let mut Y = &point[1];
        let mut Z = &point[2];

        // Defining b' - the twist coefficient
        let params = X.c0.params.clone();
        let b_twist_real = BN256Fq::from_str(B_TWIST_COEFF_REAL).unwrap();
        let b_twist_real = BN256BaseNNField::allocated_constant(cs, b_twist_real, &params);

        let b_twist_imaginary = BN256Fq::from_str(B_TWIST_COEFF_IMAGINARY).unwrap();
        let b_twist_imaginary =
            BN256BaseNNField::allocated_constant(cs, b_twist_imaginary, &params);

        let mut b_twist = BN256Fp2NNField::new(b_twist_real, b_twist_imaginary);

        // c0 <- -2 * Y * Z * y_P
        let mut c0 = Y.mul(cs, &mut Z);
        let mut c0 = c0.mul_c0(cs, &mut at.y);
        let mut c0 = c0.double(cs);
        let c0 = c0.negated(cs);

        // c1 <- 3b' * Z^2 - Y^2
        let mut z2 = Z.square(cs);
        let mut z2 = z2.mul(cs, &mut b_twist);
        let mut c1 = z2.double(cs);
        let mut c1 = c1.add(cs, &mut z2);
        let mut y2 = Y.square(cs);
        let c1 = c1.sub(cs, &mut y2);

        // c2 <- 3 * X^2 * x_P
        let mut x2 = X.square(cs);
        let mut c2 = x2.mul_c0(cs, &mut at.x);
        let mut c2 = c2.double(cs);
        let c2 = c2.add(cs, &mut x2);

        self.c0 = c0;
        self.c1 = c1;
        self.c2 = c2;
        self
    }

    pub fn as_tuple(&self) -> (BN256Fp2NNField<F>, BN256Fp2NNField<F>, BN256Fp2NNField<F>) {
        (self.c0.clone(), self.c1.clone(), self.c2.clone())
    }
}

pub struct MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    accumulated_f: BN256Fp12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    #[allow(non_snake_case)]
    pub fn evaluate(
        cs: &mut CS,
        p: &BN256Fp2ProjectiveCurvePoint<F>,
        q: &BN256Fp2ProjectiveCurvePoint<F>,
    ) -> Self {
        let params = p.x.params.clone();
        let mut f1 = BN256Fp12NNField::one(cs, &params);
        let r = q;

        for u in CURVE_PARAMETER_WNAF {
            let tangent_fn = LineFunctionEvaluation::new(cs, &params).at_tangent(cs, &r, p);
            let (mut c0, mut c1, mut c4) = tangent_fn.as_tuple();
            f1 = f1.square(cs);
            f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);
            // r = r.double(cs);

            if u == 1 {
                let line_fn = LineFunctionEvaluation::new(cs, &params).at_line(cs, &r, &q, p);
                let (mut c0, mut c1, mut c4) = line_fn.as_tuple();
                f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);
                // r = r.add(q);
            }
            if u == -1 {
                // q negated
                let line_fn = LineFunctionEvaluation::new(cs, &params).at_line(cs, &r, &q, p);
                let (mut c0, mut c1, mut c4) = line_fn.as_tuple();
                f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);
                // r = r.sub(q);
            }
        }

        Self {
            accumulated_f: f1,
            _marker: std::marker::PhantomData::<CS>,
        }
    }
}
