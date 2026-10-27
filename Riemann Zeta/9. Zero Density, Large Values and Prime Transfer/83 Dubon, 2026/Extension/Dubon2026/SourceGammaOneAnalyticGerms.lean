import Dubon2026.SourceGammaOneRatioRealization
import Dubon2026.SourceModularRatioGerms

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> finite
meromorphic germs. The native analytic identity theorem gives punctured
nonvanishing for actual modular denominators. Reuse the existing coordinate
filter identity; no new topology or valuation framework is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ModularRatios
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

end
end Dubon2026.SourceFunctionField.GammaOne.ModularRatios
