use self::traits::group_point::EllipticGroupPoint;

use super::*;
use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
    pairing::{
        self,
        ff::{Field, PrimeField},
        GenericCurveAffine,
    },
};
use std::{marker::PhantomData, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExtendedAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: pairing::ff::PrimeField,
{
    x: NF,
    y: NF,
    pub is_infinity: Boolean<F>,
    pub _marker: PhantomData<GC>,
}

impl<F, GC, NF> EllipticGroupPoint<F, GC, NF> for ExtendedAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Initializes a new non-infinite affine point with the specified coordinates
    fn new<CS>(cs: &mut CS, x: NF, y: NF) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self {
            x,
            y,
            is_infinity: Boolean::allocated_constant(cs, false),
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

    /// Initializes the point at infinity. x and y are set to zero, and is_infinity is set to true.
    fn infinity<CS>(cs: &mut CS, params: &Arc<NF::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero_nf = NF::allocated_constant(cs, GC::Base::zero(), params);

        Self {
            x: zero_nf.clone(),
            y: zero_nf,
            is_infinity: Boolean::allocated_constant(cs, true),
            _marker: PhantomData,
        }
    }

    /// Adds two affine points on the curve.
    fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // If x's are not the same, adding via unequal_x method
        let same_x = self.same_x(cs, other);
        let boolean_false = Boolean::allocated_constant(cs, false);
        if same_x == boolean_false {
            return self.add_unequal_x(cs, other);
        }

        // If y's are the same, doubling the point
        let same_y = self.same_y(cs, other).negated(cs);
        if same_y == boolean_false {
            return self.double(cs);
        }

        Self::infinity(cs, &self.x.get_params())
    }

    /// Subtracts two affine points on the curve.
    fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut negated_other = other.negate(cs);
        self.add(cs, &mut negated_other)
    }

    /// Multiplies the affine point by a scalar.
    fn mul<CS>(&mut self, cs: &mut CS, scalar: &GC::Base) -> Self
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

    /// Doubling the point X (that is, finding 2X = X + X)
    fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Validatoring that y1 is not zero
        let is_zero = self.y.is_zero(cs);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &is_zero, &boolean_false);

        // Algorithm for doubling a point (x1, y1):
        // First, finding slope = (3 * x1^2 + a) / (2 * y1)
        // Then, finding x3 = slope^2 - 2 * x1 and y3 = slope * (x1 - x3) - y1

        // Getting parameter a
        let params = self.x.get_params().clone();
        let a = GC::a_coeff();
        let mut a_nf = NF::allocated_constant(cs, a, &params);

        // Calculating nominator
        let mut nominator = self.x.clone().square(cs);
        // Multiplying by 3
        let mut initial_nominator = nominator.clone();
        nominator = nominator.double(cs);
        nominator = nominator.add(cs, &mut initial_nominator);
        // Adding a
        nominator = nominator.add(cs, &mut a_nf);

        // Calculating denominator
        let mut denominator = self.y.clone();
        // Multiplying by 2
        denominator = denominator.double(cs);

        // Calculating slope
        let mut slope = nominator.div_unchecked(cs, &mut denominator);

        // Finding x3
        let mut x = slope.clone().square(cs);
        x = x.sub(cs, &mut self.x);
        x = x.sub(cs, &mut self.x);

        // Finding y3
        let mut y = self.x.sub(cs, &mut x);
        y = slope.mul(cs, &mut y);
        y = y.sub(cs, &mut self.y);

        self.x = x;
        self.y = y;
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }

    /// Negates the point by negating the y coordinate
    fn negate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.y = self.y.negated(cs);

        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }
}

impl<F, GC, NF> ExtendedAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Returns a boolean that is true if the x coordinates of the two points are equal.
    pub fn same_x<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        self.x.equals(cs, &mut other.x)
    }

    /// Returns a boolean that is true if the y coordinates of the two points are equal.
    pub fn same_y<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        self.y.equals(cs, &mut other.y)
    }

    /// Adds two affine points elementwise.
    pub fn elementwise_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.x = self.x.add(cs, &mut other.x);
        self.y = self.y.add(cs, &mut other.y);
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }

    /// Adds two points with unequal x coordinates. If the x coordinates are equal, the result is undefined
    /// and therefore the panic is raised.
    pub fn add_unequal_x<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Verify that the x coordinates are not equal
        let same_x = self.same_x(cs, other);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &same_x, &boolean_false);

        // Algorithm for having two points (x1, y1) and (x2, y2) and adding them together:
        // First, finding slope = (y2 - y1) / (x2 - x1)
        // Then, finding x3 = slope^2 - x1 - x2 and y3 = slope * (x1 - x3) - y1
        let mut dx = self.x.sub(cs, &mut other.x);
        let mut dy = self.y.sub(cs, &mut other.y);
        // slope = dy / dx and we do not care whether dx is zero or not since we have already checked that
        let mut slope = dy.div_unchecked(cs, &mut dx);

        // x3 = slope^2 - x1 - x2
        let mut x = slope.clone().square(cs);
        x = x.sub(cs, &mut self.x);
        x = x.sub(cs, &mut other.x);

        // y3 = slope * (x1 - x3) - y1
        let mut y = self.x.sub(cs, &mut x);
        y = slope.mul(cs, &mut y);
        y = y.sub(cs, &mut self.y);

        self.x = x;
        self.y = y;
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }
}

// This is unfinished version, which does not yet compile.
#[cfg(test)]
mod tests {
    use std::alloc::Global;

    use super::*;
    use crate::{
        config::CSConfig,
        cs::{
            gates::{ConstantsAllocatorGate, FmaGateInBaseFieldWithoutConstant, NopGate},
            implementations::pow::NoPow,
            oracle::TreeHasher,
            CircuitResolverOpts, CSGeometry,
        },
        field::goldilocks::GoldilocksField,
        gadgets::{
            non_native_field::{
                ext_k_squared, ExtFqkCycField, ExtFqkField, ExtFqkFieldParams, ExtFqkFieldRoot,
                ExtFieldElement,
            },
            traits::non_native_field::NonNativeField,
        },
        pairing::traits::elliptic_curve::GenericCurveAffine,
        worker::Worker,
    };

    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::gadgets::traits::witnessable::WitnessHookable;


    type F = GoldilocksField;

    const MAX_VARIABLES: usize = 1 << 20;
    const MAX_TRACE_LEN: usize = 1 << 16;

    fn configure_builder<
        T: CsBuilderImpl<F, T>,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    >(
        builder: CsBuilder<T, F, GC, TB>,
    ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        builder
    }

    fn setup_points<CS: ConstraintSystem<F>>(
        cs: &mut CS,
    ) -> (
        ExtendedAffinePoint<F, ExtFqkCycField<F, 2, 2>, ExtFieldElement<F, 2, 2>>,
        ExtendedAffinePoint<F, ExtFqkCycField<F, 2, 2>, ExtFieldElement<F, 2, 2>>,
        ExtFqkField<F, 2, 2>,
    ) {
        let params = ExtFqkFieldParams::<F, 2, 2>::new();
        let root = ExtFqkFieldRoot::<F, 2, 2>::new(params.clone());
        let nf = ExtFqkField::<F, 2, 2>::new(params.clone());

        let x1 = nf.allocate_checked(cs, root.to_representation());
        let y1 = nf.allocate_checked(cs, root.to_representation().square());

        let x2 = nf.allocate_checked(cs, root.to_representation().square());
        let y2 = nf.allocate_checked(cs, root.to_representation().pow(4));

        let p1 = ExtendedAffinePoint::<F, ExtFqkCycField<F, 2, 2>, ExtFieldElement<F, 2, 2>>::new(
            cs, x1, y1,
        );
        let p2 = ExtendedAffinePoint::<F, ExtFqkCycField<F, 2, 2>, ExtFieldElement<F, 2, 2>>::new(
            cs, x2, y2,
        );

        (p1, p2, nf)
    }

    #[test]
    fn test_point_addition() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, MAX_TRACE_LEN);
       
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure_builder(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(MAX_VARIABLES));

        let cs = &mut owned_cs;

        let (mut p1, mut p2, nf) = setup_points(cs);

        let p3 = p1.add(cs, &mut p2);
        let params = nf.get_params();
        let root = ExtFqkFieldRoot::<F, 2, 2>::new(params.clone());
        let expected_x3 = nf.allocate_checked(cs, root.to_representation().pow(6));
        let expected_y3 = nf.allocate_checked(cs, root.to_representation().pow(7));
        assert!(p3.x.equals(cs, &expected_x3).unwrap());
        assert!(p3.y.equals(cs, &expected_y3).unwrap());

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_point_doubling() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, MAX_TRACE_LEN);
        
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure_builder(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(MAX_VARIABLES));

        let cs = &mut owned_cs;

        let (mut p1, _, nf) = setup_points(cs);

        let p4 = p1.double(cs);
        let params = nf.get_params();
        let root = ExtFqkFieldRoot::<F, 2, 2>::new(params.clone());
        let expected_x4 = nf.allocate_checked(cs, root.to_representation().pow(8));
        let expected_y4 = nf.allocate_checked(cs, root.to_representation().pow(9));
        assert!(p4.x.equals(cs, &expected_x4).unwrap());
        assert!(p4.y.equals(cs, &expected_y4).unwrap());

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_point_negation() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, MAX_TRACE_LEN);
        
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure_builder(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(MAX_VARIABLES));

        let cs = &mut owned_cs;

        let (mut p1, _, nf) = setup_points(cs);

        let p5 = p1.negate(cs);
        let x1 = p1.x.clone();
        let y1 = p1.y.clone();
        let expected_x5 = x1;
        let expected_y5 = y1.negated(cs);
        assert!(p5.x.equals(cs, &expected_x5).unwrap());
        assert!(p5.y.equals(cs, &expected_y5).unwrap());

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_scalar_multiplication() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, MAX_TRACE_LEN);
        
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure_builder(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(MAX_VARIABLES));

        let cs = &mut owned_cs;

        let (mut p1, _, nf) = setup_points(cs);

        let scalar = GoldilocksField::from_u64_unchecked(42);
        let p6 = p1.mul(cs, &scalar);
        let params = nf.get_params();
        let root = ExtFqkFieldRoot::<F, 2, 2>::new(params.clone());
        let expected_x6 = nf.allocate_checked(cs, root.to_representation().pow(10));
        let expected_y6 = nf.allocate_checked(cs, root.to_representation().pow(11));
        assert!(p6.x.equals(cs, &expected_x6).unwrap());
        assert!(p6.y.equals(cs, &expected_y6).unwrap());

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }
}