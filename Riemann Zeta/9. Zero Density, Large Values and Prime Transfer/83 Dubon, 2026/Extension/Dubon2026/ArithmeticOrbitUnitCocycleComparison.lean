import Dubon2026.ArithmeticOrbitUnitBaseChange

/-! # Original Mackey unit cocycles are genuine orbit-field base change

This compares the exact two-cocycle values, including the actual unit
embedding and conjugation. It supplies the coefficient-map identification
needed before applying local invariant corestriction on DUB-17's route
from rational to number-field reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The original arithmetic union carries its proved Galois structure. -/
local instance orbitUnitComparisonGlobalGalois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a
/-- The literal rational unit representation retains the given original topology. -/
local instance orbitUnitComparisonRawTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
  inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a))
/-- The retained topology on the literal original unit coefficient is discrete. -/
local instance orbitUnitComparisonRawDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
  inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a))

/-- Reindex the original relative unit cocycle by the actual fixing
subgroup, with the arithmetic representation written explicitly. -/
def rationalArithmeticOrbitRestrictedUnitCocycle
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (rationalArithmeticUnitRepresentation a)
        (rationalArithmeticOrbitFixingSubgroup a F).subtype) := by
  change continuousRepresentationCocyclesTwo
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) F.fixingSubgroup.subtype)
  exact galoisFixingUnitCocycle ℚ (rationalUnramifiedExtension a) F y

/-- The literal unit value of the original Mackey orbit cocycle after
the original arithmetic coefficient embedding. -/
def rationalArithmeticOrbitUnitCocycleValue
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (z : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c ×
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) c) :
    Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  rationalArithmeticUnitLocalMap a p hp
    (cosetOrbitCocycle (rationalArithmeticUnitRepresentation a)
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c
      (rationalArithmeticOrbitRestrictedUnitCocycle a F y).val z)

/-- These are exactly the values of the continuous orbit cocycle used
in the proved arithmetic Mackey formula. -/
theorem rationalArithmeticOrbitUnitCocycleValue_eq_continuous
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (z : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c ×
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) c) :
    rationalArithmeticOrbitUnitCocycleValue a p hp F c y z =
      rationalArithmeticUnitLocalMap a p hp
        ((continuousCosetOrbitCocycle (rationalArithmeticUnitRepresentation a)
          (rationalArithmeticUnitAction_continuous a)
          (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous
          (rationalArithmeticOrbitFixingSubgroup a F) c
          (rationalArithmeticOrbitRestrictedUnitCocycle a F y)).val z) := rfl

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]

/-- The actual local-field base-change cocycle equals the literal Mackey
orbit cocycle after the original global-to-local unit embedding. -/
theorem rationalArithmeticOrbitUnitCocycle_eq_baseChange
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (d e : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c) :
    (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y).val
        (rationalArithmeticOrbitLocalAutomorphism a p hp F c d,
          rationalArithmeticOrbitLocalAutomorphism a p hp F c e) =
      rationalArithmeticOrbitUnitCocycleValue a p hp F c y (d, e) := by
  rw [rationalArithmeticOrbitUnitBaseChangeCocycle_apply,
    rationalArithmeticOrbitBaseChangeRestriction, rationalArithmeticOrbitBaseChangeRestriction]
  rfl

end
end Dubon2026
