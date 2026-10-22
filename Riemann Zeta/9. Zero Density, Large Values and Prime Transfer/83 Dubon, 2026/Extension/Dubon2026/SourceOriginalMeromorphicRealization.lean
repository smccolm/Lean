import Dubon2026.SourceModularRatioGerms

/-! DUB-17/18 -> matching cusp-form lower dimension -> analytic
realization of the actual original field. The proved modular quotient
representation supplies meromorphic germs at every upper-half-plane
point, and a nonzero original element has finite germ order. No analytic
realization or denominator premise remains on these original consumers.
Normalized analytic places and the regular-differential cusp condition
remain subsequent obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology Manifold

theorem realize_eventuallyEq_of_ratio {N : ℕ} {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (x : LaurentSeries ℂ)
    (hh : h ≠ 0) (hx : x * ModularRatios.qL h = ModularRatios.qL g) (τ : ℍ) :
    (fun z : ℂ => realize N x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => g (ofComplex z) / h (ofComplex z) := by
  filter_upwards [ModularRatios.eventually_ne_zero_ofComplex h hh τ] with z hz
  exact realize_eq_div N g h x hx (ofComplex z) hz

theorem meromorphicAt_original_realize (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) := by
  obtain ⟨k, g, h, hh, hx⟩ := original_field_modular_ratio N x
  exact ((ModularRatios.analyticAt_comp_ofComplex g τ).meromorphicAt.div
    (ModularRatios.analyticAt_comp_ofComplex h τ).meromorphicAt).congr
      (realize_eventuallyEq_of_ratio g h x hh hx τ).symm

theorem meromorphicOrderAt_original_realize_ne_top (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx0 : x ≠ 0) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨k, g, h, hh, hx⟩ := original_field_modular_ratio N x
  have hval : (x : LaurentSeries ℂ) ≠ 0 := fun he => hx0 (Subtype.ext he)
  have hg : g ≠ 0 := by
    intro hg0
    have hqg : ModularRatios.qL g = 0 := by
      simp only [hg0, ModularRatios.qL, ModularForm.coe_zero,
        UpperHalfPlane.qExpansion_zero, PowerSeries.coe_zero]
    exact (mul_ne_zero hval (ModularRatios.qL_ne_zero h hh)) (hx.trans hqg)
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_original_realize N x τ)).mpr
  filter_upwards [realize_eventuallyEq_of_ratio g h x hh hx τ,
    ModularRatios.eventually_ne_zero_ofComplex g hg τ,
    ModularRatios.eventually_ne_zero_ofComplex h hh τ] with z he hg' hh'
  rw [he]
  exact div_ne_zero hg' hh'

end
end Dubon2026.SourceFunctionField
