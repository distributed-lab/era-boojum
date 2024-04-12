use std::sync::Arc;

use pairing::{bn256::G2Affine as BN256G2Affine, ff::PrimeField, GenericCurveAffine};

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{
        boolean::Boolean,
        curves::SmallField,
        non_native_field::traits::{CurveCompatibleNonNativeField, NonNativeField},
        tower_extension::{
            algebraic_torus::TorusWrapper,
            fq6::Fq6,
            params::{bn256::BN256Extension12Params, Extension12Params},
        },
    },
};

use super::*;

// Curve parameter for the BN256 curve
const CURVE_PARAMETER: &str = "4965661367192848881";
const CURVE_DIV_2_PARAMETER: &str = "2482830683596424440";
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
    c0: BN256Fq2NNField<F>,
    c3: BN256Fq2NNField<F>,
    c4: BN256Fq2NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// Creates a new instance of the line function evaluation for the BN256 curve.
    pub fn new(c0: BN256Fq2NNField<F>, c3: BN256Fq2NNField<F>, c4: BN256Fq2NNField<F>) -> Self {
        Self {
            c0,
            c3,
            c4,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// Creates a zero instance of the line function evaluation for the BN256 curve.
    pub fn zero(cs: &mut CS, params: &Arc<BN256BaseNNFieldParams>) -> Self {
        Self {
            c0: BN256Fq2NNField::zero(cs, params),
            c3: BN256Fq2NNField::zero(cs, params),
            c4: BN256Fq2NNField::zero(cs, params),
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `L_{P,Q}(R)` when `P` and `Q` are distinct points on the twisted curve
    /// `E'(F_{p^2})` and `R` is a point on the regular curve `E(F_p)`. For details,
    /// see _Section 3_ in https://eprint.iacr.org/2019/077.pdf.
    #[allow(non_snake_case)]
    pub fn at_line(
        &mut self,
        cs: &mut CS,
        point1: &mut BN256SWProjectivePointTwisted<F>,
        point2: &mut BN256SWProjectivePointTwisted<F>,
        at: &mut BN256SWProjectivePoint<F>,
    ) -> Self {
        // c0 <- (X - Z * X2) * y_P
        let mut z_x2 = point1.x.mul(cs, &mut point2.z);
        let mut x_sub_z_x2 = point2.x.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_c0(cs, &mut at.y);

        // c4 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = point2.z.mul(cs, &mut point1.y);
        let mut y_sub_z_y2 = point2.y.sub(cs, &mut z_y2);
        let mut c4 = point1.x.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = point1.y.mul(cs, &mut x_sub_z_x2);
        let c4 = c4.sub(cs, &mut y2_x_sub_z_x2);

        // c3 <- -(Y - Z * Y2) * x_P
        let mut c3 = y_sub_z_y2.negated(cs);
        let c3 = c3.mul_c0(cs, &mut at.x);

        Self::new(c0, c3, c4)
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `L_{P,P}(R)` when `P` is a point on the twisted curve `E'(F_{p^2})` and
    /// `R` is a point on the regular curve `E(F_p)`. For details,
    /// see _Section 3_ in https://eprint.iacr.org/2019/077.pdf.
    #[allow(non_snake_case)]
    pub fn at_tangent(
        &mut self,
        cs: &mut CS,
        point: &mut BN256SWProjectivePointTwisted<F>,
        at: &mut BN256SWProjectivePoint<F>,
    ) -> Self {
        // Defining b' - the twist coefficient
        let params = point.x.c0.params.clone();
        let mut b_twist = BN256Fq2NNField::from_curve_base(cs, &BN256G2Affine::b_coeff(), &params);

        // c0 <- -2 * Y * Z * y_P
        let mut c0 = point.y.mul(cs, &mut point.z);
        let mut c0 = c0.mul_c0(cs, &mut at.y);
        let mut c0 = c0.double(cs);
        let c0 = c0.negated(cs);

        // c4 <- 3b' * Z^2 - Y^2
        let mut z2 = point.z.square(cs);
        let mut z2 = z2.mul(cs, &mut b_twist);
        let mut c4 = z2.double(cs);
        let mut c4 = c4.add(cs, &mut z2);
        let mut y2 = point.y.square(cs);
        let c4 = c4.sub(cs, &mut y2);

        // c3 <- 3 * X^2 * x_P
        let mut x2 = point.x.square(cs);
        let mut c3 = x2.mul_c0(cs, &mut at.x);
        let mut c3 = c3.double(cs);
        let c3 = c3.add(cs, &mut x2);

        Self::new(c0, c3, c4)
    }
}

/// Struct for the miller loop evaluation for the BN256 curve.
/// Here, the Miller loop returns the accumulated f value after the loop
/// without the final exponentiation.
pub struct MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    accumulated_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// This function computes the Miller loop for the BN256 curve, using
    /// algorithm from _Section 2_ from https://eprint.iacr.org/2016/130.pdf.
    pub fn evaluate(
        cs: &mut CS,
        p: &mut BN256SWProjectivePoint<F>,
        q: &mut BN256SWProjectivePointTwisted<F>,
    ) -> Self {
        // Setting evaluation parameters
        let params = p.x.params.clone();
        let mut evaluation = LineFunctionEvaluation::zero(cs, &params);

        let mut f1 = BN256Fq12NNField::one(cs, &params);
        let mut r = q.clone();

        for u in CURVE_PARAMETER_WNAF {
            // Doubling step: f1 <- f1^2 * L_{R,R}(P), R <- 2R
            let mut tan_fn = evaluation.at_tangent(cs, &mut r, p);
            f1 = f1.square(cs);
            f1 = Self::mul_f12_by_line_fn(cs, &mut f1, &mut tan_fn);
            r = r.double(cs);

            // Skip if u is zero
            if u == 0 {
                continue;
            }

            // Addition step: f1 <- f1 * L_{R,Q}(P), R <- R + Q.
            // If u is negative, negate Q.
            let mut q = q.clone();
            if u == -1 {
                q = q.negated(cs);
            }

            let mut line_fn = evaluation.at_line(cs, &mut r, &mut q, p);
            f1 = Self::mul_f12_by_line_fn(cs, &mut f1, &mut line_fn);

            let qx = q.x.clone();
            let qy = q.y.clone();
            r = r.add_mixed(cs, &mut (qx, qy));
        }

        Self {
            accumulated_f: f1,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    fn mul_f12_by_line_fn(
        cs: &mut CS,
        f: &mut BN256Fq12NNField<F>,
        line_fn: &mut LineFunctionEvaluation<F, CS>,
    ) -> BN256Fq12NNField<F> {
        f.mul_by_c0c3c4(cs, &mut line_fn.c0, &mut line_fn.c3, &mut line_fn.c4)
    }
}

pub struct FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    resultant_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// This function computes the final exponentiation for the BN256 curve.
    pub fn evaluate(cs: &mut CS, f: &mut BN256Fq12NNField<F>) -> Self {
        let (mut easy_part_torus, is_trivial) = Self::easy_part(cs, f);
        let mut hard_part_torus = Self::hard_part(cs, &mut easy_part_torus);

        let not_trivial = is_trivial.negated(cs);
        let resultant_f = hard_part_torus.mask(cs, &not_trivial);
        let resultant_f = resultant_f.decompress(cs);

        Self {
            resultant_f,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// This function computes the easy part of the final exponentiation, that is
    /// for given f \in `F_{p^{12}}` it computes `f^{(p^6-1)(p^2+1)}`.
    pub fn easy_part(cs: &mut CS, f: &mut BN256Fq12NNField<F>) -> (BN256Fq12Torus<F>, Boolean<F>) {
        // We use that one-time torus compression cost can be absorbed directly in the easy part computation as follows:
        // let m = m0 + w * m1 \in Fp12 be the Miller loop result, then:
        // m^{p^6−1} = (m0 + w*m1)^{p^6−1} = (m0 + w*m1)^{p^6} / (m0 + w*m1) = (m0 − w*m1)/(m0 + w*m1) =
        // = (−m0/m1 + w)/(−m0/m1 − w) = Dec(-m0/m1)
        // Hence: Enc(m^{(p^6-1)(p^2+1)}) = Enc(Dec(-m0/m1)^{p^2+1}) = (-m0/m1)^{p^2+1} = [[(-m0/m1)^{p^2) * (-m0/m1)]]
        // where all multiplications and power-maps inside [[ ]] are treated as operations on T2.

        // We need to implement custom conversion m = m0 + w * m1 \in Fp12 -> -m0/m1 \in T2.
        // If m1 == 0 \then m actually belongs to \Fp6, and hence m^{p^6−1} = 1
        // in this case we replace m by generator of order d = hard_part_exp

        let params = f.c0.c0.get_params();

        let exception = Fq6::is_zero(&mut f.c1, cs);
        let one = Fq6::one(cs, params);
        let c1 = Fq6::conditionally_select(cs, exception, &one, &f.c1);
        let f: BN256Fq12NNField<F> = Fq12::new(f.c0.clone(), c1);

        // actual value of compressed element is (m0 − w*m1)/(m0 + w*m1)
        // the result of Miller loop belongs to Fp12* and hence is never zero,
        // hence m0 and m1 can't be zero simultaneously

        let mut dividend = f.c0.clone();
        let mut divisor = f.c1.clone();
        let encoding = dividend.div(cs, &mut divisor);

        let mut x = TorusWrapper::new(encoding);
        let mut y = x.clone().frobenius_map(cs, 2);
        let mut candidate = x.mul(cs, &mut y);
        let gen = Self::get_hard_part_generator();
        let (res, enc_is_zero) = candidate.replace_by_constant_if_trivial(cs, gen);
        let is_trivial = exception.or(cs, enc_is_zero);

        (res, is_trivial)
    }

    /// Computes the hard part of the final exponentiation using method by Aranha et al.
    /// For details, see https://eprint.iacr.org/2016/130.pdf, _Algorithm 2_.
    pub fn hard_part(cs: &mut CS, f: &mut BN256Fq12Torus<F>) -> BN256Fq12Torus<F> {
        let u = BN256Fq::from_str(CURVE_PARAMETER).unwrap();
        let u_div_2 = BN256Fq::from_str(CURVE_DIV_2_PARAMETER).unwrap();

        // 1. t0 <- f^2; 2. t1 <- t0^u; 3. t2 <- t1^(u/2);
        // 4. t3 <- f^(-1); 5. t1 <- t3*t1.
        let mut t0 = f.square(cs);
        let mut t1 = t0.pow(cs, u);
        let mut t2 = t1.pow(cs, u_div_2);
        let mut t3 = f.inverse(cs);
        let mut t1 = t3.mul(cs, &mut t1);

        // 6. t1 <- t1^{-1}; 7. t1 <- t1*t2
        let mut t1 = t1.inverse(cs);
        let mut t1 = t1.mul(cs, &mut t2);

        // 8. t2 <- t1^u
        let mut t2 = t1.pow(cs, u);

        // 9. t3 <- t2^u; 10. t1 <- t1^{-1}; 11. t3 <- t1*t3
        let mut t3 = t2.pow(cs, u);
        let mut t1 = t1.inverse(cs);
        let mut t3 = t1.mul(cs, &mut t3);

        // 12. t1 <- t1^{-1}; 13. t1 <- t1^{p^3}; 14. t2 <- t2^{p^2};
        // 15. t1 <- t1*t2
        let mut t1 = t1.inverse(cs);
        let mut t1 = t1.frobenius_map(cs, 3);
        let mut t2 = t2.frobenius_map(cs, 2);
        let mut t1 = t1.mul(cs, &mut t2);

        // 16. t2 <- t3^u; 17. t2 <- t2*t0; 18. t2 <- t2*f
        let mut t2 = t3.pow(cs, u);
        let mut t2 = t2.mul(cs, &mut t0);
        let mut t2 = t2.mul(cs, f);

        // 19. t1 <- t1*t2; 20. t2 <- t3^p; 21. t1 <- t1*t2
        let mut t1 = t1.mul(cs, &mut t2);
        let mut t2 = t3.frobenius_map(cs, 1);
        let t1 = t1.mul(cs, &mut t2);

        t1
    }

    fn get_hard_part_generator() -> <BN256Extension12Params as Extension12Params<BN256Fq>>::Witness
    {
        todo!()
    }
}

/// This function computes the pairing function for the BN256 curve.
pub fn ec_pairing<F, CS>(
    cs: &mut CS,
    p: &mut BN256SWProjectivePoint<F>,
    q: &mut BN256SWProjectivePointTwisted<F>,
) -> BN256Fq12NNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut miller_loop = MillerLoopEvaluation::evaluate(cs, p, q);
    let final_exp = FinalExpEvaluation::evaluate(cs, &mut miller_loop.accumulated_f);
    final_exp.resultant_f
}
