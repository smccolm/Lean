import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Injective original arithmetic source-class comparison

The literal finite-stage comparison is injective and commutes with the
original transitions. Direct-limit zero detection therefore proves that
the original arithmetic source classes embed in full classes modulo outside
units. Surjectivity and class formation remain separate DUB-17 obligations.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual arithmetic source-class comparison is injective by original finite-stage zero detection. -/
theorem arithmeticSourceClassColimitComparison_injective :
    Function.Injective (arithmeticSourceClassColimitComparison K Ω a ha).hom := by
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
  have hm := arithmeticSourceClassColimitComparison_of K Ω a ha E y
  change (arithmeticSourceClassColimitComparison K Ω a ha).hom
    ((coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) E).hom y) = 0 at hx
  rw [hm] at hx
  obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx
  have hF' : (arithmeticSourceClassStageComparison K Ω a ha F).hom
      (arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF y) = 0 :=
    (arithmeticSourceClassStageComparison_natural K Ω a ha E F hEF y).symm.trans hF
  have hy : arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF y = 0 :=
    arithmeticSourceClassStageComparison_injective K Ω a ha F
      (hF'.trans (map_zero (arithmeticSourceClassStageComparison K Ω a ha F).hom).symm)
  change Module.DirectLimit.of ℤ _ (fun F => ArithmeticSPlaceClassFiniteStageRep K Ω a ha F)
    (arithmeticSPlaceClassTransitionMap K Ω a ha) E y = 0
  rw [← Module.DirectLimit.of_f (hij := hEF), hy, map_zero]

end
end Dubon2026
