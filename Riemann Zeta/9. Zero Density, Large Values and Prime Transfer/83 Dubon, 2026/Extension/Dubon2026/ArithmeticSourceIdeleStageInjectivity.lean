import Dubon2026.ArithmeticGlobalSourceColimits
import Dubon2026.OriginalSPlaceBaseChangeInjective

/-! # Faithful finite stages for the actual source-idele cup

The existing injectivity of the literal S-place field transition makes
the source-idele coefficient lift faithful. This preserves the cocycle
identity when descending the source cup to a finite arithmetic stage,
before comparing its full-class image and normalized local sum for DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- Each actual source-idele transition is injective at the original support. -/
theorem arithmeticSPlaceTransitionMap_injective
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    Function.Injective (arithmeticSPlaceTransitionMap K Ω a ha E F hEF) := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  exact originalSPlaceBaseChange_injective E F _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual finite source-idele stage embeds in its original arithmetic colimit. -/
theorem arithmeticSPlaceColimitOf_injective
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Function.Injective (coefficientRepresentationColimitOf
      (arithmeticGlobalSPlaceStageRep K Ω a ha)
      (arithmeticGlobalSPlaceStageTransition K Ω a ha) E).hom := by
  letI : DirectedSystem (fun F => arithmeticGlobalSPlaceStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalSPlaceStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticSPlaceDirectedSystem K Ω a ha
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticGlobalSPlaceStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalSPlaceStageTransition K Ω a ha E F h).hom.toLinearMap)
    E x = 0 at hx
  obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx
  apply arithmeticSPlaceTransitionMap_injective K Ω a ha E F hEF
  exact hF.trans (map_zero _).symm

end
end Dubon2026
