use pairing::{ff::PrimeField, BitIterator};
use std::sync::Arc;

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{
        boolean::Boolean,
        non_native_field::traits::NonNativeField,
        traits::selectable::Selectable,
    },
};

use super::{fq12::Fq12, fq2::Fq2, fq6::Fq6, params::TorusExtension12Params};

/// [`TorusWrapper`] is an algebraic compression of the `Fq12` element via underlying encoding of `Fq6`.
/// In compressed form operations over Fq12 are less expensive.
///
/// The implementation is based on the following paper:
/// https://eprint.iacr.org/2022/1162.pdf.
#[derive(Clone, Debug, Copy)]
pub struct TorusWrapper<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: TorusExtension12Params<T>,
{
    pub encoding: Fq6<F, T, NN, P::Ex6>,
}

// TODO: Probably, this could be implemented generally for any two Fqk and Fq(k/2) elements.
impl<F: SmallField, T: PrimeField, NN: NonNativeField<F, T>, P: TorusExtension12Params<T>>
    TorusWrapper<F, T, NN, P>
{
    /// Creates a new instance of the [`TorusWrapper`] with the given encoding.
    pub fn new(encoding: Fq6<F, T, NN, P::Ex6>) -> Self {
        Self { encoding }
    }

    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let encoding = Fq6::zero(cs, params);
        Self::new(encoding)
    }

    /// Returns the underlying parameters of the encoded `Fq6` element.
    pub fn get_params(&self) -> &Arc<NN::Params> {
        self.encoding.get_params()
    }

    /// Normalizes the encoding of the `Fq6` element.
    pub fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.encoding.normalize(cs);
    }

    /// Returns an instance if `flag` is `true`, otherwise returns a zero element.
    pub fn mask<CS>(&mut self, cs: &mut CS, flag: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fq6::zero(cs, self.get_params());
        let new_encoding =
            <Fq6<F, T, NN, P::Ex6>>::conditionally_select(cs, flag, &self.encoding, &zero);

        Self::new(new_encoding)
    }

    /// Compresses the `Fq12` element `c0 + c1*w` to the Torus (`T2`) element.
    ///
    /// Uses the formula `m <- (1 + c0) / c1` to compress the `Fq12` element with the additional
    /// check for the exceptional case when `c1` is zero.
    ///
    /// If `SAFE=false`, then the function will not check for the exceptional case when `c1` is zero.
    pub fn compress<CS, const SAFE: bool>(cs: &mut CS, f: &mut Fq12<F, T, NN, P>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = f.get_params();
        let mut c0 = f.c0.clone();
        let mut c1 = f.c1.clone();

        let mut encoding = if SAFE {
            // Preparing flags for exception cases
            let is_exceptional = Fq6::is_zero(&mut c1, cs);
            let mut c0_is_one = Fq6::one(cs, params);
            let c0_is_one = c0_is_one.equals(cs, &mut c0);
            let mut is_exceptional = Fq6::from_boolean(cs, is_exceptional, params);
            let mut c0_is_one = Fq6::from_boolean(cs, c0_is_one, params);

            // m <- (1 + c0) / c1 if c1 is non-zero. However, to account for the case where
            // c1 is zero, we set numerator to 1 + c0 - 2*c0_is_one and denominator to c1 + is_exceptional.
            let mut numerator = Fq6::one(cs, params);
            let mut numerator = numerator.add(cs, &mut c0);
            let mut c0_is_one_doubled = c0_is_one.double(cs);
            let mut numerator = numerator.sub(cs, &mut c0_is_one_doubled);
            let mut denominator = f.c1.add(cs, &mut is_exceptional);
            denominator.normalize(cs);

            let encoding = numerator.div(cs, &mut denominator);
            encoding
        } else {
            // Verifying that c1 is non-zero
            let boolean_false = Boolean::allocated_constant(cs, false);
            let c1_is_zero = c1.is_zero(cs);
            Boolean::enforce_equal(cs, &c1_is_zero, &boolean_false);

            // m <- (1 + c0) / c1
            let mut encoding = Fq6::one(cs, params);
            let mut encoding = encoding.add(cs, &mut f.c0);
            let encoding = encoding.div(cs, &mut f.c1);

            encoding
        };

        encoding.normalize(cs);
        Self::new(encoding)
    }

    /// Decompresses the Torus (`T2`) element `g` back to the `Fq12` element by using the formula
    ///
    /// `zeta^{-1} = (g + w)/(g - w)`
    pub fn decompress<CS>(&self, cs: &mut CS) -> Fq12<F, T, NN, P>
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut one = Fq6::one(cs, params);
        let negative_one = one.negated(cs);

        // Since `g` is a pure `Fq6` element, `g+w` is just an `Fq12` element with `c0 = g` and `c1 = 1`.
        let mut numerator = Fq12::new(self.encoding.clone(), one);
        // Since `g` is a pure `Fq6` element, `g-w` is just an `Fq12` element with `c0 = g` and `c1 = -1`.
        let mut denominator = Fq12::new(self.encoding.clone(), negative_one);

        // zeta^{-1} = (g + w)/(g - w)
        let decompressed = numerator.div(cs, &mut denominator);

        decompressed
    }

    /// Computes the inverse of the Torus element using the formula g -> -g.
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let encoding = self.encoding.negated(cs);
        Self::new(encoding)
    }

    /// Computes the conjugate of the Torus element using the formula g -> -g.
    /// Note that the conjugate of the Torus element is the same as its inverse.
    pub fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.inverse(cs)
    }

    /// Computes the Frobenius map of the Torus element with the given power using the formula
    ///
    /// frob_map(g, i) = g^(p^i) / \gamma^{(p^i-1)/2}
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        // Numerator is simply frob_map(g, i)
        let mut g = self.encoding.clone();
        let mut numerator = g.frobenius_map(cs, power);

        // Since w^2 = \gamma, that means \gamma^{1/2} = w and therefore
        // \gamma^{(p^i-1)/2} = w^{p^i-1} = frob_map(w, i)*w^{-1}. Thus,
        // denominator is frob_map(w, i)*w^{-1}

        // First, allocating the w^{-1}
        let w_inverse = P::get_w_inverse_coeffs_c6();
        let mut w_inverse = Fq2::constant(cs, w_inverse, params);
        // Then, computing frob_map(w, i)*w^{-1}
        let mut w: Fq12<F, T, NN, P> = Fq12::one_imaginary(cs, params);
        let mut denominator = w.frobenius_map(cs, power);
        let mut denominator = denominator.mul_by_c6(cs, &mut w_inverse);

        // Asserting that c1 is zero since denominator must be a pure Fq6 element.
        let boolean_true = Boolean::allocated_constant(cs, true);
        let c1_is_zero = denominator.c1.is_zero(cs);
        Boolean::enforce_equal(cs, &c1_is_zero, &boolean_true);
        let mut denominator = denominator.c0.clone();
        denominator.normalize(cs);

        // frob_map(g, i) / \gamma^{(p^i-1)/2}
        let mut encoding = numerator.div(cs, &mut denominator);
        encoding.normalize(cs);
        Self::new(encoding)
    }

    /// Computes the product of two Torus elements using the formula
    ///
    /// `(g, g') -> (g * g' + \gamma) / (g + g')`
    ///
    /// The formula handles the exceptional case when `g + g'` is zero.
    pub fn mul<CS, const SAFE: bool>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut one = Fq2::one(cs, params);

        // g1 <- g, g2 <- g'
        let mut g1 = self.encoding.clone();
        let mut g2 = other.encoding.clone();

        // x <- g * g' + \gamma
        let mut x = g1.mul(cs, &mut g2);
        // Adding gamma to x
        x.c1 = x.c1.add(cs, &mut one);
        // y <- g + g'
        let mut y = g1.add(cs, &mut g2);

        let encoding = if SAFE {
            // Exception occurs when g = -g'. To account for such case,
            // the following formula is used (where flag = (y == 0)? 1 : 0 --- exception case):
            // result <- (x - flag * x) / (g + g' + flag)

            let mut zero = Fq6::zero(cs, params);
            let exception = y.equals(cs, &mut zero);
            let mut flag = Fq6::from_boolean(cs, exception, params);

            let mut numerator = flag.mul(cs, &mut x);
            let mut numerator = x.sub(cs, &mut numerator);
            let mut denominator = y.add(cs, &mut flag);
            let result = numerator.div(cs, &mut denominator);
            result
        } else {
            // Here we do not check whether g = -g' since the function is unsafe
            let result = x.div(cs, &mut y);
            result
        };

        Self::new(encoding)
    }

    pub fn pow_naf_decomposition<CS, S: AsRef<[i8]>, const SAFE: bool>(
        &mut self,
        cs: &mut CS,
        decomposition: S,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Intializing the result with 1
        let mut result = Self::one(cs, self.get_params());

        // Preparing self and self inverse in advance
        let mut self_cloned = self.clone();
        let mut self_inverse = self.conjugate(cs);

        for bit in decomposition.as_ref().iter() {
            result = result.square::<_, SAFE>(cs);

            // If bit is 1, multiply by initial torus
            let bit_is_one = Boolean::allocated_constant(cs, *bit == 1);
            let result_times_self = result.mul::<_, SAFE>(cs, &mut self_cloned);
            result = Self::conditionally_select(cs, bit_is_one, &result_times_self, &result);

            // If bit is -1, multiply by inverse initial torus
            let bit_is_minus_one = Boolean::allocated_constant(cs, *bit == -1);
            let result_times_self_inverse = result.mul::<_, SAFE>(cs, &mut self_inverse);
            result = Self::conditionally_select(
                cs,
                bit_is_minus_one,
                &result_times_self_inverse,
                &result,
            );
        }

        result
    }

    pub fn pow_u32<CS, S: AsRef<[u64]>>(&mut self, cs: &mut CS, exponent: S) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut result = Self::one(cs, self.get_params());
        let mut found_one = false;

        for bit in BitIterator::new(exponent) {
            let apply_squaring = Boolean::allocated_constant(cs, found_one);
            let result_squared = result.square::<_, true>(cs);
            result = Self::conditionally_select(cs, apply_squaring, &result_squared, &result);
            if !found_one {
                found_one = bit;
            }

            let result_multiplied = result.mul::<_, true>(cs, self);
            let apply_multiplication = Boolean::allocated_constant(cs, bit);
            result =
                Self::conditionally_select(cs, apply_multiplication, &result_multiplied, &result);

            result.normalize(cs);
        }

        result
    }

    /// Squares the Torus element using the formula
    ///
    /// `g -> (1/2)(g + \gamma/g)`
    ///
    /// The formula handles the exceptional case when `g` is zero.
    pub fn square<CS, const SAFE: bool>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut g = self.encoding.clone();

        // Calculating \gamma/g safely
        let mut exception_term = if SAFE {
            // Exception occurs when g = 0. To account for such case,
            // the following formula is used (flag = (g == 0)? 1 : 0 --- exception case):
            // result <- (1/2)(g + (\gamma*(1-flag)) / (g + flag))

            let mut zero = Fq6::zero(cs, params);
            let exception = g.equals(cs, &mut zero);
            let mut flag = Fq6::from_boolean(cs, exception, params);

            let mut result = g.add(cs, &mut flag);
            let mut result = result.inverse(cs);
            let result = result.mul_by_nonresidue(cs);

            <Fq6<F, T, NN, P::Ex6>>::conditionally_select(cs, exception, &zero, &result)
        } else {
            // Here we do not check whether g = 0 since the function is unsafe
            let mut result = g.inverse(cs);
            result.mul_by_nonresidue(cs)
        };

        // Calculating (1/2)(g + \gamma/g)
        let mut encoding = g.add(cs, &mut exception_term);
        
        // Allocating 2^{-1}
        let two_inverse = P::get_two_inverse_coeffs_c0();
        let mut two_inverse = NN::allocated_constant(cs, two_inverse, params);

        // Calculating (1/2)(g + \gamma/g)
        encoding = encoding.mul_by_fq(cs, &mut two_inverse);

        Self::new(encoding)
    }
}

impl<F, T, NN, P> Selectable<F> for TorusWrapper<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: TorusExtension12Params<T>,
{
    fn conditionally_select<CS>(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let encoding =
            <Fq6<F, T, NN, P::Ex6>>::conditionally_select(cs, flag, &a.encoding, &b.encoding);

        Self::new(encoding)
    }
}
