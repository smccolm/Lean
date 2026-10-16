import Dubon2026.ArithmeticOrbitIndexFiniteness
import Dubon2026.ArithmeticUnitCorestrictionOrbits
import Dubon2026.ArithmeticOrbitTraceCompletionInvariant

/-! # Prime localization of genuine field corestriction is the actual Mackey sum

Apply the existing continuous arithmetic Mackey theorem to the literal
fixing-subgroup cocycle of the original field class. The existing same-value
trace comparison identifies its corestriction with genuine field
corestriction. All finite index instances are constructed from the actual
finite field. This is DUB-17's invariant-sum assembly input.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype arithmeticOrbitCompletionCosets

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [tA : TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [dA : DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [tF : TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [dF : DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [tB : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [dB : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Localization of the original field corestriction is exactly the sum of its literal local Mackey terms. -/
theorem rationalArithmeticUnitCorestriction_primeRestriction
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    rationalArithmeticUnitH2Restriction a p hp
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F),
          rationalArithmeticOrbitUnitTrace a p hp F ω.out y := by
  have htrace := @galoisUnitContinuousCorestriction_eq_subgroupTrace ℚ (rationalUnramifiedExtension a)
    _ _ _ _ F _ _ tA dA tF dF
    F.fixingSubgroup F.fixingSubgroup_isOpen (arithmeticOrbitGlobalCosetsFintype a F) rfl
    (rationalArithmeticOrbitRestrictedUnitCocycle a F y) y (fun _ _ => rfl)
  have h := rationalArithmeticUnitH2_restriction_corestriction_orbits a p hp
    (rationalArithmeticOrbitFixingSubgroup a F) F.fixingSubgroup_isOpen
    (rationalArithmeticOrbitRestrictedUnitCocycle a F y)
  exact (congrArg (rationalArithmeticUnitH2Restriction a p hp) htrace.symm).trans h

end
end Dubon2026
