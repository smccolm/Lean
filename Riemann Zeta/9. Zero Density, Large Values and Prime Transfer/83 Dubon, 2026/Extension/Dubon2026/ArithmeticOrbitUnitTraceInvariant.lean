import Dubon2026.ArithmeticOrbitUnitTraceEquality
import Dubon2026.ArithmeticOrbitLocalStructure
import Dubon2026.LocalFieldContinuousInvariantCorestriction

/-! # The actual invariant of an arithmetic Mackey orbit summand

The literal trace is genuine orbit-field corestriction, so the repo's
proved local corestriction theorem identifies its normalized invariant
with that of the original field-base-changed class. The required local
structures exist by the preceding spectral construction. Identification
with the individual number-field completion remains a distinct DUB-17 edge.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [ValuativeRel (rationalArithmeticOrbitLocalField a p hp F c)]
  [TopologicalSpace (rationalArithmeticOrbitLocalField a p hp F c)]
  [IsNonarchimedeanLocalField (rationalArithmeticOrbitLocalField a p hp F c)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F c))]
  [Fintype (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸
    cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c)]

/-- The normalized invariant of the original Mackey orbit summand is
the genuine local-field invariant of its original field-base-changed class. -/
theorem rationalArithmeticOrbitUnitTrace_invariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
        (rationalArithmeticOrbitUnitTrace a p hp F c y) =
      localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitLocalField a p hp F c)
        (rationalPrimeLocalClosure p hp)
        (Submodule.Quotient.mk (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y)) := by
  have h := congrArg
    (localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
    (rationalArithmeticOrbitUnitCorestriction_eq_field a p hp F c y)
  exact h.trans (localFieldContinuousH2InvariantEquiv_corestriction
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
    (rationalArithmeticOrbitLocalField a p hp F c)
    (Submodule.Quotient.mk (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y)))

end
end Dubon2026
