import Dubon2026.ContinuousAdjointGeneralComparison
import Dubon2026.ContinuousTraceZeroRestriction
import Dubon2026.ContinuousCohomologyRestriction
import Dubon2026.ContinuousCohomologyCoefficientCongr
import Dubon2026.AdjointRepresentationRestriction

/-! # Exact comparison of generic and original deformation cohomology restriction -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Generic continuous H1 restriction becomes exactly the original deformation
restriction after the proved equality of the actual adjoint coefficient actions. -/
theorem continuousMatrixAdjointH1GeneralEquiv_restriction
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j) (x : ContinuousMatrixAdjointH1 ρ hρ) :
    continuousH1CoefficientCongr (matrixAdjointRepresentation_comp ρ j)
      (restrictedCoefficientAction_continuous (matrixAdjointRep ρ) j hj
        (matrixAdjointAction_continuous ρ hρ))
      (matrixAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
      (continuousRepresentationH1Restriction (matrixAdjointRep ρ)
        (matrixAdjointAction_continuous ρ hρ) j hj
        (continuousMatrixAdjointH1GeneralEquiv ρ hρ x)) =
      continuousMatrixAdjointH1GeneralEquiv (ρ.comp j) (hρ.comp hj)
        (continuousMatrixAdjointH1Restriction ρ hρ j hj x) := by
  induction x using Quotient.inductionOn' with
  | h c =>
    change continuousH1CoefficientCongr (matrixAdjointRepresentation_comp ρ j)
      _ _ (Submodule.Quotient.mk (continuousRepresentationCocycleOneRestriction
        (matrixAdjointRep ρ) j hj ⟨c.val, c.property⟩)) =
      Submodule.Quotient.mk (continuousMatrixAdjointRestriction ρ j hj c)
    rw [continuousH1CoefficientCongr_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro h
    exact continuousCocycleOneCoefficientCongr_apply (matrixAdjointRepresentation_comp ρ j) _ h

section TraceZero

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- The generic continuous H1 restriction also recovers the exact original
trace-zero deformation restriction, without replacing its coefficient action. -/
theorem continuousTraceZeroH1GeneralEquiv_restriction
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousH1CoefficientCongr (matrixTraceZeroAdjointRepresentation_comp ρ j)
      (restrictedCoefficientAction_continuous (matrixTraceZeroAdjointRep ρ) j hj
        (matrixTraceZeroAdjointAction_continuous ρ hρ))
      (matrixTraceZeroAdjointAction_continuous (ρ.comp j) (hρ.comp hj))
      (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj
        (continuousTraceZeroH1GeneralEquiv ρ hρ x)) =
      continuousTraceZeroH1GeneralEquiv (ρ.comp j) (hρ.comp hj)
        (continuousTraceZeroH1Restriction ρ hρ j hj x) := by
  induction x using Quotient.inductionOn' with
  | h c =>
    change continuousH1CoefficientCongr (matrixTraceZeroAdjointRepresentation_comp ρ j)
      _ _ (Submodule.Quotient.mk (continuousRepresentationCocycleOneRestriction
        (matrixTraceZeroAdjointRep ρ) j hj ⟨c.val, c.property⟩)) =
      Submodule.Quotient.mk (continuousTraceZeroAdjointRestriction ρ j hj c)
    rw [continuousH1CoefficientCongr_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro h
    exact continuousCocycleOneCoefficientCongr_apply
      (matrixTraceZeroAdjointRepresentation_comp ρ j) _ h

end TraceZero
end
end Dubon2026
