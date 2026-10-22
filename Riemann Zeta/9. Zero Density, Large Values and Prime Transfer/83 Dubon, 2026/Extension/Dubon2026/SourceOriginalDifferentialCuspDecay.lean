import Dubon2026.SourceOriginalDifferentialSlashBound

/-! DUB-17/18 -> regular-differential cusp forms -> decay at every cusp.
The continuous power estimate, E4 -> 1 and Delta -> 0 prove vanishing
of every weight-two slash translate of the original regular differential.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularForm KaehlerDifferential SourceCurve
open scoped Topology BigOperators MatrixGroups ModularForm Manifold

theorem tendsto_zero_of_norm_pow {α : Type*} {l : Filter α} (f : α → ℂ) (m : ℕ)
    (h : Tendsto (fun x => ‖f x‖ ^ m) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h.eventually_lt_const (pow_pos hε m)] with x hx
  rw [dist_zero_right]
  by_contra hnot
  have he := pow_le_pow_left₀ hε.le (le_of_not_gt hnot) m
  exact (not_lt_of_ge he) hx

theorem tendsto_zero_of_modular_power_bound (F : ℍ → ℂ) (M : ℕ) (B : ℝ)
    (hb : ∀ᶠ τ : ℍ in atImInfty,
      ‖F τ‖ ^ (2 * M) * ‖E₄ τ‖ ^ (3 * (M + 1)) ≤
        B * ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ (4 * M)) :
    IsZeroAtImInfty F := by
  have h4 : Tendsto (fun τ : ℍ => ‖E₄ τ‖) atImInfty (𝓝 1) := by
    simpa only [norm_one] using JMultiplicity.tendsto_E₄_atImInfty.norm
  have hΔ : Tendsto (fun τ : ℍ => ‖ModularForm.discriminant τ‖) atImInfty (𝓝 0) := by
    simpa only [norm_zero] using JMultiplicity.tendsto_discriminant_atImInfty.norm
  have hlim : Tendsto (fun τ : ℍ =>
      (B * ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ (4 * M)) /
        ‖E₄ τ‖ ^ (3 * (M + 1))) atImInfty (𝓝 0) := by
    simpa only [one_pow, mul_zero, zero_mul, zero_div] using
      ((hΔ.const_mul B).mul (h4.pow (4 * M))).div (h4.pow (3 * (M + 1))) (by simp)
  apply tendsto_zero_of_norm_pow F (2 * M)
  apply squeeze_zero' (Eventually.of_forall fun τ => pow_nonneg (norm_nonneg _) _) _ hlim
  filter_upwards [hb, JMultiplicity.tendsto_E₄_atImInfty.eventually_ne
    (by norm_num : (1 : ℂ) ≠ 0)] with τ hτ hne
  exact (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hne) _)).mpr hτ

theorem original_regular_differential_cusp_decay (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (F : ℍ → ℂ) (hF : MDiff F)
    (he : ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ))
    (γ : SL(2, ℤ)) : IsZeroAtImInfty (F ∣[(2 : ℤ)] γ) := by
  obtain ⟨B, _, hB⟩ := original_regular_differential_slash_power_bound N x hx hreg g h hh hr F hF he
  exact tendsto_zero_of_modular_power_bound _ (SourceLevelProjective.dedekindPsi N) B (hB γ)

end
end Dubon2026.SourceFunctionField
