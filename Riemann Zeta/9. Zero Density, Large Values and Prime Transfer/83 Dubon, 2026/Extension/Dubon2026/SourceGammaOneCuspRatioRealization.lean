import Dubon2026.SourceGammaOneTranslatedCuspGerms
import Dubon2026.SourceGammaOneMeromorphicRealization

/-! DUB-17/18 -> actual Gamma1 regular-differential/cusp converse ->
actual cusp order. The original modular quotient has a meromorphic germ
at every translated cusp, with finite order for nonzero field elements.
All denominator and germ hypotheses are derived from actual modular forms. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups ModularForm Topology Manifold
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

/-- The cusp function of the actual modular quotient at a translated cusp. -/
def cuspRealize (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (N : ℕ) (γ : SL(2, ℤ)) (x : LaurentSeries ℂ) : ℂ → ℂ :=
  cuspFunction N (fun τ : ℍ => realize Γ x (γ • τ))

theorem realize_smul_eq_translated_ratio (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (x : LaurentSeries ℂ)
    (hx : x * ModularRatios.qL h = ModularRatios.qL g) (γ : SL(2, ℤ)) (τ : ℍ)
    (hτ : ModularForm.translate h (γ : GL (Fin 2) ℝ) τ ≠ 0) :
    realize Γ x (γ • τ) = ModularForm.translate g (γ : GL (Fin 2) ℝ) τ /
      ModularForm.translate h (γ : GL (Fin 2) ℝ) τ := by
  have hh : h (γ • τ) ≠ 0 := by
    intro he
    apply hτ
    change ((h : ℍ → ℂ) ∣[k] γ) τ = 0
    rw [ModularForm.SL_slash_apply, he, zero_mul]
  rw [realize_eq_div Γ hT g h x hx (γ • τ) hh]
  change g (γ • τ) / h (γ • τ) = ((g : ℍ → ℂ) ∣[k] γ) τ / ((h : ℍ → ℂ) ∣[k] γ) τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply,
    mul_div_mul_right _ _ (zpow_ne_zero _ (denom_ne_zero γ τ))]

theorem cuspRealize_eventuallyEq_of_ratio (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (x : LaurentSeries ℂ)
    (hh : h ≠ 0) (hx : x * ModularRatios.qL h = ModularRatios.qL g) (γ : SL(2, ℤ)) :
    cuspRealize Γ N γ x =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspFunction N (ModularForm.translate g (γ : GL (Fin 2) ℝ)) /
        cuspFunction N (ModularForm.translate h (γ : GL (Fin 2) ℝ)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_zero_translated_cuspFunction N hΓ h hh γ] with q hq hden
  simp only [cuspRealize, cuspFunction,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.div_apply] at hden ⊢
  exact realize_smul_eq_translated_ratio hT g h x hx γ _ hden

theorem meromorphicAt_cuspRealize (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspRealize Γ N γ (x : LaurentSeries ℂ)) 0 := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  exact ((analyticAt_translated_cuspFunction N hΓ g γ).meromorphicAt.div
    (analyticAt_translated_cuspFunction N hΓ h γ).meromorphicAt).congr
      (cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hx γ).symm

theorem meromorphicOrderAt_cuspRealize_ne_top (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (hx0 : x ≠ 0) (γ : SL(2, ℤ)) :
    meromorphicOrderAt (cuspRealize Γ N γ (x : LaurentSeries ℂ)) 0 ≠ ⊤ := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  have hval : (x : LaurentSeries ℂ) ≠ 0 := fun he => hx0 (Subtype.ext he)
  have hg : g ≠ 0 := by
    intro hg0
    have hqg : ModularRatios.qL g = 0 := by
      simp only [hg0, ModularRatios.qL, ModularForm.coe_zero, qExpansion_zero, PowerSeries.coe_zero]
    exact (mul_ne_zero hval (ModularRatios.qL_ne_zero hT h hh)) (hx.trans hqg)
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (meromorphicAt_cuspRealize N hΓ hT x γ)).mpr
  filter_upwards [cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hx γ,
    eventually_ne_zero_translated_cuspFunction N hΓ g hg γ,
    eventually_ne_zero_translated_cuspFunction N hΓ h hh γ] with q he hg' hh'
  rw [he, Pi.div_apply]
  exact div_ne_zero hg' hh'

end
end Dubon2026.SourceFunctionField.GammaOne
