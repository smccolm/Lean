import Dubon2026.ArithmeticOrbitUnitCocycleComparison
import Dubon2026.GaloisUnitCorestrictionCocycleComparison

/-! # The original continuous orbit and field trace maps

These are the literal Mackey trace and genuine orbit-field corestriction
on the same original coefficients. Their equality is proved in the next
module using the preceding fixing-subgroup and cocycle identities. It
serves the normalized invariant comparison on DUB-17's reciprocity chain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The actual continuous Mackey orbit cocycle after its original
global-to-local coefficient map. -/
def rationalArithmeticOrbitLocalUnitCocycle
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep
        (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
        (cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F) c).subtype) := by
  let A := rationalArithmeticUnitRepresentation a
  let B := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  let j := rationalPrimeArithmeticRestriction a p hp
  let S := rationalArithmeticOrbitFixingSubgroup a F
  let H := cosetOrbitStabilizer j.toMonoidHom S c
  exact continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (restrictedCoefficientRep A j.toMonoidHom) H.subtype)
    (restrictedCoefficientRep B H.subtype)
    (rationalArithmeticUnitLocalMap a p hp) continuous_of_discreteTopology
    (fun g x => rationalArithmeticUnitLocalMap_equivariant a p hp g x)
    (continuousCosetOrbitCocycle A (rationalArithmeticUnitAction_continuous a)
      j.toMonoidHom j.continuous S c (rationalArithmeticOrbitRestrictedUnitCocycle a F y))

/-- The actual continuous coefficient map retains precisely the proved orbit-cocycle values. -/
theorem rationalArithmeticOrbitLocalUnitCocycle_apply
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (d e : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c) :
    (rationalArithmeticOrbitLocalUnitCocycle a p hp F c y).val (d, e) =
      rationalArithmeticOrbitUnitCocycleValue a p hp F c y (d, e) := rfl

variable [FiniteDimensional ℚ F]

/-- Finiteness of the actual orbit field is derived from the original finite global field. -/
local instance arithmeticOrbitComparisonLocalFinite :
    FiniteDimensional (rationalPrimeLocalField p hp) (rationalArithmeticOrbitLocalField a p hp F c) :=
  rationalArithmeticOrbitLocalField_finiteDimensional a p hp F c

/-- The actual Mackey summand, defined by its original continuous
coset trace and original coefficient-mapped orbit cocycle. -/
def rationalArithmeticOrbitUnitTrace
    [Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
      cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F) c)]
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    GaloisUnitContinuousH2 (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) :=
  continuousRepresentationH2Corestriction
        (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
        (discreteGaloisUnitAction_continuous (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))
        (cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F) c)
        (cosetOrbitStabilizer_isOpen (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous
          (rationalArithmeticOrbitFixingSubgroup a F) F.fixingSubgroup_isOpen c)
        (Submodule.Quotient.mk (rationalArithmeticOrbitLocalUnitCocycle a p hp F c y))

/-- The same original closure units retain their topology when the fixed field changes. -/
local instance arithmeticOrbitComparisonLocalTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
      (rationalPrimeLocalClosure p hp)) :=
  inferInstanceAs (TopologicalSpace
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))
/-- That retained original unit topology is discrete. -/
local instance arithmeticOrbitComparisonLocalDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
      (rationalPrimeLocalClosure p hp)) :=
  inferInstanceAs (DiscreteTopology
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))

/-- Genuine orbit-field corestriction of the original field-base-changed cocycle. -/
def rationalArithmeticOrbitFieldTrace
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    GaloisUnitContinuousH2 (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) :=
  galoisUnitContinuousCorestriction (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticOrbitLocalField a p hp F c)
    (Submodule.Quotient.mk (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y))

end
end Dubon2026
