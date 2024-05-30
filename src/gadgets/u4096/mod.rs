use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::witnessable::CSWitnessable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;
use crypto_bigint::U2048;
use u2048::UInt2048;

use crate::config::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt4096<F: SmallField> {
    pub inner: [UInt32<F>; 128],
}

pub fn decompose_u4096_as_u32x128(value: (U2048, U2048)) -> [u32; 128] {
    let low_limbs = value.0.as_limbs();
    let high_limbs = value.1.as_limbs();

    let mut result = [0u32; 128];
    // Filling the low limb
    for i in 0..32 {
        result[i * 2] = low_limbs[i].0 as u32;
        result[i * 2 + 1] = (low_limbs[i].0 >> 32) as u32;
    }
    // Filling the high limb
    for i in 0..32 {
        result[i * 2 + 64] = high_limbs[i].0 as u32;
        result[i * 2 + 1 + 64] = (high_limbs[i].0 >> 32) as u32;
    }

    result
}

pub fn recompose_u4096_as_u32x128(value: [u32; 128]) -> (U2048, U2048) {
    // Filling the low limb
    let mut low = [0u64; 32];
    for i in 0..32 {
        low[i] = (value[i * 2] as u64) | ((value[i * 2 + 1] as u64) << 32);
    }

    // Filling the high limb
    let mut high = [0u64; 32];
    for i in 0..32 {
        high[i] = (value[i * 2 + 32] as u64) | ((value[i * 2 + 1 + 32] as u64) << 32);
    }

    (U2048::from_words(low), U2048::from_words(high))
}

impl<F: SmallField> CSAllocatable<F> for UInt4096<F> {
    type Witness = (U2048, U2048);
    fn placeholder_witness() -> Self::Witness {
        (U2048::ZERO, U2048::ZERO)
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<128>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u4096_as_u32x128(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt4096<F> {
    const INTERNAL_STRUCT_LEN: usize = 128;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        // value
        recompose_u4096_as_u32x128(
            values.map(|el| <u32 as WitnessCastable<F, F>>::cast_from_source(el)),
        )
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocate_without_value(cs)
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        self.inner.map(|el| el.get_variable())
    }

    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        decompose_u4096_as_u32x128(witness)
            .map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt4096<F> {
    #[must_use]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let inner = Selectable::conditionally_select(cs, flag, &a.inner, &b.inner);

        Self { inner }
    }
}

impl<F: SmallField> UInt4096<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constant: (U2048, U2048),
    ) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_u4096_as_u32x128(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> (U2048, U2048) + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let outputs = cs.alloc_multiple_variables_without_values::<128>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 64);
                let witness = (witness_closure)(inputs);
                let chunks = decompose_u4096_as_u32x128(witness);

                output_buffer.extend(chunks.map(|el| F::from_u64_unchecked(el as u64)));
            };

            cs.set_values_with_dependencies_vararg(
                dependencies,
                &Place::from_variables(outputs),
                value_fn,
            );
        }

        let chunks = outputs.map(|el| UInt32::from_variable_checked(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocated_constant(cs, (U2048::ZERO, U2048::ZERO))
    }

    #[must_use]
    pub fn overflowing_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        let mut carry_out = Boolean::allocated_constant(cs, false);
        let mut result = *self; // any uninit would be fine too
        for ((a, b), dst) in self
            .inner
            .iter()
            .zip(other.inner.iter())
            .zip(result.inner.iter_mut())
        {
            let (c, carry) = (*a).overflowing_add_with_carry_in(cs, *b, carry_out);
            *dst = c;
            carry_out = carry;
        }

        (result, carry_out)
    }

    #[must_use]
    pub fn overflowing_sub<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        let mut borrow_out = Boolean::allocated_constant(cs, false);
        let mut result = *self; // any uninit would be fine too
        for ((a, b), dst) in self
            .inner
            .iter()
            .zip(other.inner.iter())
            .zip(result.inner.iter_mut())
        {
            let (c, borrow) = (*a).overflowing_sub_with_borrow_in(cs, *b, borrow_out);
            *dst = c;
            borrow_out = borrow;
        }

        (result, borrow_out)
    }

    /// Multiplies a number by 2^{32}. Panics if the number overflows.
    #[must_use]
    pub fn must_mul_by_two_pow_32<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let boolean_true = Boolean::allocated_constant(cs, true);
        let last_limb_zero = self.inner[127].is_zero(cs);
        Boolean::enforce_equal(cs, &last_limb_zero, &boolean_true);

        let mut new_inner = self.inner.clone();
        new_inner.copy_within(0..127, 1);
        new_inner[0] = UInt32::zero(cs);

        Self { inner: new_inner }
    }

    // Returns the value unchanges if `bit` is `true`, and 0 otherwise
    #[must_use]
    pub fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        let new_inner = self.inner.map(|el| el.mask(cs, masking_bit));
        Self { inner: new_inner }
    }

    // Returns the value unchanges if `bit` is `false`, and 0 otherwise
    #[must_use]
    pub fn mask_negated<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        masking_bit: Boolean<F>,
    ) -> Self {
        let new_inner = self.inner.map(|el| el.mask_negated(cs, masking_bit));
        Self { inner: new_inner }
    }

    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        let equals: [_; 128] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 512]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 128];
        for (dst, src) in inner.iter_mut().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_le_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn from_limbs(limbs: [UInt32<F>; 128]) -> Self {
        Self { inner: limbs }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 512]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 128];
        for (dst, src) in inner.iter_mut().rev().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_be_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        let limbs_are_zero = self.inner.map(|el| el.is_zero(cs));
        Boolean::multi_and(cs, &limbs_are_zero)
    }

    #[must_use]
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 512] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 512];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 512] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }

    #[must_use]
    pub fn to_low(self) -> UInt2048<F> {
        UInt2048 {
            inner: self.inner[..64].try_into().expect("incorrect slice size"),
        }
    }

    #[must_use]
    pub fn to_high(self) -> UInt2048<F> {
        UInt2048 {
            inner: self.inner[64..].try_into().expect("incorrect slice size"),
        }
    }
}

use crate::cs::Variable;
use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;

impl<F: SmallField> WitnessCastable<F, [F; 128]> for (U2048, U2048) {
    #[inline]
    fn cast_from_source(witness: [F; 128]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_u4096_as_u32x128(reduced)
    }

    #[inline]
    fn cast_into_source(self) -> [F; 128] {
        let limbs = decompose_u4096_as_u32x128(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 128> for UInt4096<F> {
    type ConversionFunction = Convertor<F, [F; 128], (U2048, U2048)>;

    fn witness_from_set_of_values(values: [F; 128]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 128] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt4096<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

use crate::gadgets::traits::selectable::MultiSelectable;
// multiselect doesn't make much sense here because we can do parallel over chunks,
// so we degrade to default impl via normal select
impl<F: SmallField> MultiSelectable<F> for UInt4096<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt4096<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        64
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt4096<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
