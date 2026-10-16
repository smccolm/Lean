import Dubon2026.ArithmeticOrbitUnitMackey
import Dubon2026.ArithmeticUnitPrimeInvariant

/-! # The actual corestriction invariant is the sum of genuine completion invariants

Apply the existing normalized local invariant to the proved original
field-corestriction Mackey formula. The individual completion comparison
identifies every summand with the original global unit cocycle localized
through its genuine induced prime completion. This is DUB-17's sum
assembly input before the exact original-prime reindexing.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The rational-prime invariant of genuine field corestriction is the sum of the original global class's genuine completion-localized invariants over the exact Mackey orbits. -/
theorem rationalArithmeticUnitCorestriction_primeInvariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    rationalArithmeticUnitPrimeInvariant a p hp
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F),
          localFieldContinuousH2InvariantEquiv (rationalArithmeticOrbitPrimeCompletion a p hp F ω.out)
            (rationalPrimeLocalClosure p hp)
            (Submodule.Quotient.mk (rationalArithmeticOrbitCompletionUnitCocycle a p hp F ω.out y)) := by
  let inv := localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  have hM := congrArg inv (rationalArithmeticUnitCorestriction_primeRestriction a p hp F y)
  have hS : inv (∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F), rationalArithmeticOrbitUnitTrace a p hp F ω.out y) =
      ∑ ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F), inv (rationalArithmeticOrbitUnitTrace a p hp F ω.out y) :=
    map_sum inv _ Finset.univ
  have hT := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (ω : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F)) _ =>
        rationalArithmeticOrbitUnitTrace_completion_invariant a p hp F ω.out y)
  exact hM.trans (hS.trans hT)

end
end Dubon2026
