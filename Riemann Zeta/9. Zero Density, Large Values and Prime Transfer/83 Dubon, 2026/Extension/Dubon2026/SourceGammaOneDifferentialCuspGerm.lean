import Dubon2026.SourceGammaOneCuspRatioRealization
import Dubon2026.SourceGammaOneHolomorphicDifferentials

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> cusp
vanishing. The holomorphic realization of x D(j) has, after every slash
translate, the actual cusp germ of x times the literal derivative of j. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped MatrixGroups ModularForm Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

theorem differential_cusp_germ (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hh : h ≠ 0) (x : LaurentSeries ℂ)
    (hr : x * ModularRatios.qL h = ModularRatios.qL g) (F : ℍ → ℂ)
    (he : ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ))
    (γ : SL(2, ℤ)) :
    cuspFunction N (F ∣[(2 : ℤ)] γ) =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspRealize Γ N γ x * cuspFunction N (fun τ : ℍ =>
        deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_ne_zero_translated_cuspFunction N hΓ h hh γ] with q hq hden
  simp only [cuspRealize, cuspFunction,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.mul_apply] at hden ⊢
  let τ : ℍ := ofComplex (Function.Periodic.invQParam N q)
  change ((F ∣[(2 : ℤ)] γ) τ) = realize Γ x (γ • τ) *
    deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)
  have hτ : h (γ • τ) ≠ 0 := by
    intro hz
    apply hden
    change ((h : ℍ → ℂ) ∣[k] γ) τ = 0
    rw [SL_slash_apply, hz, zero_mul]
  rw [realize_eq_div Γ hT g h x hr (γ • τ) hτ]
  have hF := (eq_div_iff hτ).mpr (he (γ • τ))
  rw [SL_slash_apply, hF, raw_j_derivative_smul]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [denom_ne_zero γ τ]

end
end Dubon2026.SourceFunctionField.GammaOne
