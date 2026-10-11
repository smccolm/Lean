import Dubon2026.ContinuousRepresentationCohomology

/-! # Continuous cohomology transport along an actual equality of coefficient actions -/

namespace Dubon2026
noncomputable section

variable {R G V : Type} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul R V]
  {ρ σ : Representation R G V} (h : ρ = σ)

/-- A proved equality of the original actions identifies the continuous
one-cocycle modules without altering the original coefficient function. -/
def continuousCocycleOneCoefficientCongr :
    continuousRepresentationCocyclesOne (Rep.of ρ) ≃ₗ[R]
      continuousRepresentationCocyclesOne (Rep.of σ) := by
  subst σ
  exact LinearEquiv.refl R _

/-- A proved equality of the original actions identifies the continuous
two-cocycle modules on the same original product topology. -/
def continuousCocycleTwoCoefficientCongr :
    continuousRepresentationCocyclesTwo (Rep.of ρ) ≃ₗ[R]
      continuousRepresentationCocyclesTwo (Rep.of σ) := by
  subst σ
  exact LinearEquiv.refl R _

omit [IsTopologicalGroup G] in
/-- The one-cocycle identification preserves the exact original function. -/
theorem continuousCocycleOneCoefficientCongr_apply
    (c : continuousRepresentationCocyclesOne (Rep.of ρ)) (g : G) :
    (continuousCocycleOneCoefficientCongr h c).val g = c.val g := by
  subst σ
  rfl

omit [IsTopologicalGroup G] in
/-- The two-cocycle identification preserves the exact original function. -/
theorem continuousCocycleTwoCoefficientCongr_apply
    (c : continuousRepresentationCocyclesTwo (Rep.of ρ)) (g : G × G) :
    (continuousCocycleTwoCoefficientCongr h c).val g = c.val g := by
  subst σ
  rfl

variable (hρ : Continuous (fun z : G × V => ρ z.1 z.2))
  (hσ : Continuous (fun z : G × V => σ z.1 z.2))

/-- Equality of the original coefficient actions identifies their genuine
continuous H1 quotients, including the same continuous coboundary relation. -/
def continuousH1CoefficientCongr :
    ContinuousRepresentationH1 (Rep.of ρ) hρ ≃ₗ[R]
      ContinuousRepresentationH1 (Rep.of σ) hσ := by
  subst σ
  exact LinearEquiv.refl R _

/-- Equality of the original coefficient actions identifies their genuine
continuous H2 quotients, including actual continuous cochain witnesses. -/
def continuousH2CoefficientCongr :
    ContinuousRepresentationH2 (Rep.of ρ) hρ ≃ₗ[R]
      ContinuousRepresentationH2 (Rep.of σ) hσ := by
  subst σ
  exact LinearEquiv.refl R _

omit [IsTopologicalGroup G] in
/-- The H1 identification uses exactly the unchanged original representative. -/
theorem continuousH1CoefficientCongr_mk
    (c : continuousRepresentationCocyclesOne (Rep.of ρ)) :
    continuousH1CoefficientCongr h hρ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneCoefficientCongr h c) := by
  subst σ
  rfl

/-- The H2 identification uses exactly the unchanged original representative. -/
theorem continuousH2CoefficientCongr_mk
    (c : continuousRepresentationCocyclesTwo (Rep.of ρ)) :
    continuousH2CoefficientCongr h hρ hσ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoCoefficientCongr h c) := by
  subst σ
  rfl

end
end Dubon2026
