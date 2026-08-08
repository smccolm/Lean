import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Statements

namespace RiemannZeta.GuthMaynard

/--
Ingham's bound for the zero density estimate.
$N(\sigma, T) \le T^{\frac{3(1-\sigma)}{2-\sigma} + o(1)}$ for $\sigma \ge 1/2$.
-/
def InghamZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 1/2 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (2 - σ)))

/--
Huxley's bound for the zero density estimate.
$N(\sigma, T) \le T^{\frac{3(1-\sigma)}{3\sigma-1} + o(1)}$ for $\sigma \ge 3/4$.
-/
def HuxleyZeroDensity (zeroCount : ℝ → ℝ → ℕ) : Prop :=
  ∀ (σ : ℝ), 3/4 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound (fun T => (zeroCount σ T : ℝ)) (fun T => T ^ (3 * (1 - σ) / (3 * σ - 1)))

/-- F-12: Combined zero density estimate transfer theorem.
    Ingham's bound supplies the required exponent for `1/2 ≤ σ ≤ 7/10`,
    while the Guth-Maynard bound supplies it for `7/10 < σ ≤ 1`.
-/
def CombinedZeroDensityTransfer : Prop :=
  ∀ (zeroCount : ℝ → ℝ → ℕ),
    InghamZeroDensity zeroCount →
    GuthMaynardZeroDensity zeroCount →
    CombinedZeroDensity zeroCount

lemma EpsilonPowerBound_mono (f g1 g2 : ℝ → ℝ) 
  (h : EpsilonPowerBound f g1)
  (h_bound : ∀ T ≥ 2, |g1 T| ≤ |g2 T|) : 
  EpsilonPowerBound f g2 := by
  intro ε hε
  have h_base := h ε hε
  have h_mono : (fun T => T ^ ε * |g1 T|) =O[Filter.atTop] (fun T => T ^ ε * |g2 T|) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop 2] with T hT
    have h1 : 0 ≤ T^ε := Real.rpow_nonneg (by linarith) _
    have h2 := h_bound T hT
    calc ‖T^ε * |g1 T|‖ = T^ε * |g1 T| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_abs]
         _ ≤ T^ε * |g2 T| := mul_le_mul_of_nonneg_left h2 h1
         _ = 1 * (T^ε * |g2 T|) := by ring
         _ = 1 * ‖T^ε * |g2 T|‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_abs]
  exact h_base.trans h_mono

/-- F-12: Kernel-checked combination of the two explicitly supplied zero-density bounds. -/
theorem combined_zero_density_transfer_native : CombinedZeroDensityTransfer := by
  intro zeroCount hIngham hGuthMaynard σ h_half h_one
  by_cases h_710 : σ ≤ 7/10
  · have hIng := hIngham σ h_half h_one
    apply EpsilonPowerBound_mono _ _ _ hIng
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hd1 : 0 < 2 - σ := by linarith
    have h1 : 3 * (1 - σ) / (2 - σ) ≤ 30 * (1 - σ) / 13 := by
      rw [div_le_div_iff₀ hd1 (by norm_num)]
      nlinarith
    exact h1
  · push Not at h_710
    have hGM := hGuthMaynard σ (by linarith) h_one
    apply EpsilonPowerBound_mono _ _ _ hGM
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hd2 : 0 < 3 + 5 * σ := by linarith
    have h2 : 15 * (1 - σ) / (3 + 5 * σ) ≤ 30 * (1 - σ) / 13 := by
      rw [div_le_div_iff₀ hd2 (by norm_num)]
      nlinarith
    exact h2

end RiemannZeta.GuthMaynard
