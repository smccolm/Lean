import Dubon2026.TraceZeroCharacterCohomologyRestriction

/-! # Actual character-valued trace cups commute with original deformation restriction -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- The literal character-valued trace cup commutes with restriction of the
original twisted H1 and the original trace-zero deformation H1. This uses the
proved action equalities and the existing original deformation restriction. -/
theorem matrixTraceZeroCharacterH1Cup_restriction
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
      (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    coefficientCharacterH2Restriction χ hχ j hj
        (matrixTraceZeroCharacterH1Cup ρ hρ χ hχ x y) =
      matrixTraceZeroCharacterH1Cup (ρ.comp j) (hρ.comp hj) (χ.comp j) (hχ.comp hj)
        (matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj x)
        (continuousTraceZeroH1Restriction ρ hρ j hj y) := by
  induction x using Quotient.inductionOn' with
  | h f =>
    induction y using Quotient.inductionOn' with
    | h u =>
      change coefficientCharacterH2Restriction χ hχ j hj
        (matrixTraceZeroCharacterH1Cup ρ hρ χ hχ
          (Submodule.Quotient.mk f) (Submodule.Quotient.mk u)) =
        matrixTraceZeroCharacterH1Cup (ρ.comp j) (hρ.comp hj) (χ.comp j) (hχ.comp hj)
          (Submodule.Quotient.mk (matrixTraceZeroCharacterCocycleRestriction ρ χ j hj f))
          (Submodule.Quotient.mk (continuousTraceZeroAdjointRestriction ρ j hj u))
      rw [matrixTraceZeroCharacterH1Cup_mk, coefficientCharacterH2Restriction_mk,
        matrixTraceZeroCharacterH1Cup_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change matrixTraceZeroTracePairing (f.val (j z.1))
        ((matrixTraceZeroAdjointRep ρ).ρ (j z.1) (u.val (j z.2))) =
        matrixTraceZeroTracePairing
          ((matrixTraceZeroCharacterCocycleRestriction ρ χ j hj f).val z.1)
          ((matrixTraceZeroAdjointRep (ρ.comp j)).ρ z.1 (u.val (j z.2)))
      rw [matrixTraceZeroCharacterCocycleRestriction_apply]
      apply congrArg (matrixTraceZeroTracePairing (f.val (j z.1)))
      exact LinearMap.congr_fun
        (DFunLike.congr_fun (matrixTraceZeroAdjointRepresentation_comp ρ j) z.1)
        (u.val (j z.2))

end
end Dubon2026
