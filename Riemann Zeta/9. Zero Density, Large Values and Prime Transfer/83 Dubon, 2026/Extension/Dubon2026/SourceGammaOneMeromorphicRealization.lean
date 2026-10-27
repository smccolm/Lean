import Dubon2026.SourceGammaOneAnalyticGerms

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> actual
meromorphic field realization. Every field element has a proved equal-weight
modular quotient; nonzero elements have finite germ order at every point.
Adapt the proved SourceOriginalMeromorphicRealization to the original
integral-ratio field, using translation membership and no Gamma0 place. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold

theorem realize_eventuallyEq_of_ratio {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (x : LaurentSeries ℂ)
    (hh : h ≠ 0) (hx : x * ModularRatios.qL h = ModularRatios.qL g) (τ : ℍ) :
    (fun z : ℂ => realize Γ x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => g (ofComplex z) / h (ofComplex z) := by
  filter_upwards [ModularRatios.eventually_ne_zero_ofComplex h hh τ] with z hz
  exact realize_eq_div Γ hT g h x hx (ofComplex z) hz

theorem meromorphicAt_realize {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  exact ((ModularRatios.analyticAt_comp_ofComplex g τ).meromorphicAt.div
    (ModularRatios.analyticAt_comp_ofComplex h τ).meromorphicAt).congr
      (realize_eventuallyEq_of_ratio hT g h x hh hx τ).symm

theorem meromorphicOrderAt_realize_ne_top {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (hx0 : x ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  have hval : (x : LaurentSeries ℂ) ≠ 0 := fun he => hx0 (Subtype.ext he)
  have hg : g ≠ 0 := by
    intro hg0
    have hqg : ModularRatios.qL g = 0 := by
      simp only [hg0, ModularRatios.qL, ModularForm.coe_zero,
        UpperHalfPlane.qExpansion_zero, PowerSeries.coe_zero]
    exact (mul_ne_zero hval (ModularRatios.qL_ne_zero hT h hh)) (hx.trans hqg)
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_realize hT x τ)).mpr
  filter_upwards [realize_eventuallyEq_of_ratio hT g h x hh hx τ,
    ModularRatios.eventually_ne_zero_ofComplex g hg τ,
    ModularRatios.eventually_ne_zero_ofComplex h hh τ] with z he hg' hh'
  rw [he]
  exact div_ne_zero hg' hh'

end
end Dubon2026.SourceFunctionField.GammaOne
