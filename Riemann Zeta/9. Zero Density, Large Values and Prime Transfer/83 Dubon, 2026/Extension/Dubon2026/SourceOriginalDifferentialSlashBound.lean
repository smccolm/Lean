import Dubon2026.SourceInverseJDerivativePower
import Dubon2026.SourceCuspBoundExtension

/-! DUB-17/18 -> regular-differential cusp forms -> decay at every cusp.
The actual holomorphic differential and inverse-j bound imply a continuous
power estimate for every slash translate, including denominator zeros.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularForm KaehlerDifferential SourceCurve
open scoped Topology BigOperators MatrixGroups ModularForm Manifold

theorem holomorphic_differential_slash_off_zeros (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (F : ℍ → ℂ)
    (he : ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ))
    (γ : SL(2, ℤ)) (τ : ℍ) (hτ : h (γ • τ) ≠ 0) :
    (F ∣[(2 : ℤ)] γ) τ = (g (γ • τ) / h (γ • τ)) *
      deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  have hF := (eq_div_iff hτ).mpr (he (γ • τ))
  rw [SL_slash_apply, hF, raw_j_derivative_smul]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [denom_ne_zero γ τ]

theorem differential_slash_power_bound (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (F : ℍ → ℂ)
    (he : ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ))
    (c : ℂ) (hc : ∀ τ : ℍ, deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) =
      c * E₄ τ ^ 2 * E₆ τ / ModularForm.discriminant τ)
    (M : ℕ) (C : ℝ) (γ : SL(2, ℤ)) (τ : ℍ) (h4 : E₄ τ ≠ 0)
    (hτ : h (γ • τ) ≠ 0)
    (hY : ‖inverseJExpression M (g (γ • τ) / h (γ • τ)) (JMultiplicity.jf τ)‖ ≤ C) :
    ‖(F ∣[(2 : ℤ)] γ) τ‖ ^ (2 * M) * ‖E₄ τ‖ ^ (3 * (M + 1)) ≤
      ‖c‖ ^ (2 * M) * C * ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ (4 * M) := by
  have hp := raw_j_derivative_power c hc M (g (γ • τ) / h (γ • τ)) τ h4
  rw [← holomorphic_differential_slash_off_zeros N g h F he γ τ hτ] at hp
  have heq := congrArg norm ((eq_div_iff (pow_ne_zero _ h4)).mp hp)
  simp only [norm_mul, norm_pow] at heq
  rw [heq]
  gcongr

theorem original_regular_differential_slash_power_bound (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (F : ℍ → ℂ) (hF : MDiff F)
    (he : ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ γ : SL(2, ℤ), ∀ᶠ τ : ℍ in atImInfty,
      ‖(F ∣[(2 : ℤ)] γ) τ‖ ^ (2 * SourceLevelProjective.dedekindPsi N) *
          ‖E₄ τ‖ ^ (3 * (SourceLevelProjective.dedekindPsi N + 1)) ≤
        B * ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ (4 * SourceLevelProjective.dedekindPsi N) := by
  let M := SourceLevelProjective.dedekindPsi N
  obtain ⟨c, hc0, hc⟩ := exists_raw_j_derivative_formula
  obtain ⟨C, hC, hY⟩ := original_regular_inverse_j_analytic_bound N x hx hreg g h hh hr
  refine ⟨‖c‖ ^ (2 * M) * C, mul_pos (pow_pos (norm_pos_iff.mpr hc0) _) hC, ?_⟩
  intro γ
  apply eventually_le_of_punctured_nonzero
    (((hF.slash 2 (γ : GL (Fin 2) ℝ)).continuous.norm.pow (2 * M)).mul
      (E₄.holo'.continuous.norm.pow (3 * (M + 1))))
    ((continuous_const.mul CuspForm.discriminant.holo'.continuous.norm).mul
      (E₄.holo'.continuous.norm.pow (4 * M)))
    (eventually_ne_zero_modular_translate N h hh γ)
  filter_upwards [hY, JMultiplicity.tendsto_E₄_atImInfty.eventually_ne
    (by norm_num : (1 : ℂ) ≠ 0)] with τ hYτ h4
  intro hτ
  exact differential_slash_power_bound N g h F he c hc M C γ τ h4 hτ (hYτ γ hτ)

end
end Dubon2026.SourceFunctionField
