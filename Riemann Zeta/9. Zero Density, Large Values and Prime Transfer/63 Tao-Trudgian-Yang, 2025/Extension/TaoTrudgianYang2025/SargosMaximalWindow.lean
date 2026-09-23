import TaoTrudgianYang2025.SargosPowerCompletion
import TaoTrudgianYang2025.SargosMomentCentral

/-! The actual maximal even moment is bounded by the literal source near count. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuartic_maximal_even_window_le_count {N p : ℕ}
    (hN : 1 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {δ lambda : ℝ} (hδ : 0 < δ) (hlambda : 0 < lambda) (c d : ℝ) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      (sargosQuarticPrefixMaximum N z α γ)^(2*p)) ≤
      (3*(1+Real.log N))^(2*p)*(16*δ*lambda)*
        (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) := by
  letI : NeZero N := ⟨by omega⟩
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  let C : ℝ := (16*δ*lambda)*
    (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ)
  have hB : 0 ≤ B := (sum_sargosPrefixMajorant_pos (N := N)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 2*p-1+1 = 2*p := by omega
  have hc := sargosQuarticMaximum_power_rectangle_le_completed (N := N)
    (2*p-1) z c (c+δ) d (d+lambda)
  rw [he] at hc
  calc
    _ ≤ B^(2*p-1)*(∑ k : ZMod N, sargosPrefixMajorant k*
        (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
          ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(2*p))) := hc
    _ ≤ B^(2*p-1)*(∑ k : ZMod N, sargosPrefixMajorant k*C) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB _)
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (sargosQuartic_even_moment_window_le_count hN p (sargosQuarticTwist z k)
          (sargosQuarticTwist_norm_le_one hz k) hδ hlambda c d)
        (sargosPrefixMajorant_nonneg k)
    _ = B^(2*p)*C := by
      rw [← Finset.sum_mul]
      change B^(2*p-1)*(B*C) = _
      rw [← mul_assoc,← pow_succ,he]
    _ ≤ (3*(1+Real.log N))^(2*p)*C :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hB (sum_sargosPrefixMajorant_le_log (N := N)) _) hC
    _ = _ := by dsimp [C]; ring

theorem sargosQuartic_maximal_even_window_transfer {N p : ℕ}
    (hN : 1 ≤ N) (hp : 1 ≤ p) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {Δ δ μ lambda : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda) (c d : ℝ) :
    (∫ α in Icc c (c+δ), ∫ γ in Icc d (d+lambda),
      (sargosQuarticPrefixMaximum N z α γ)^(2*p)) ≤
      (1024*(3*(1+Real.log N))^(2*p)*δ*lambda/(Δ*μ))*
        (∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
          ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p)) := by
  have hδp := hΔ.trans_le hδ
  have hlambdap := hμ.trans_le hlambda
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  apply (sargosQuartic_maximal_even_window_le_count hN hp z hz hδp hlambdap c d).trans
  calc
    _ ≤ (3*(1+Real.log N))^(2*p)*(16*δ*lambda)*
        ((64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
          ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p))) :=
      mul_le_mul_of_nonneg_left
        (sargosMomentNearCount_window_le_central hN p hΔ hμ hδ hlambda) (by positivity)
    _ = _ := by ring

theorem sargos_one_add_log_le_source {N : ℕ} (hN : 2 ≤ N) :
    1+Real.log (N : ℝ) ≤ (1+1/Real.log 2)*Real.log N := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNr
  have hquot : 1 ≤ Real.log (N : ℝ)/Real.log 2 := (le_div_iff₀ h2).2 (by simpa)
  calc
    _ ≤ Real.log (N : ℝ)/Real.log 2+Real.log N := add_le_add hquot le_rfl
    _ = _ := by ring

end TaoTrudgianYang2025

