import TaoTrudgianYang2025.RobertSargosZeroQSource
import TaoTrudgianYang2025.RobertSargosZeroQParameters

/-! Actual h-intersections in the zero-q column, with the endpoint replacement charged. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_mixed_correlation_bound
    (f : ℝ → ℝ) (M H : ℕ) (r : ℤ) {C lam : ℝ}
    (hr : r ≠ 0) (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hrmax : |(r:ℝ)| ≤ lam^(-(1:ℝ)/13))
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ‖robertSargosMixedCorrelation f M H 0 r‖ ≤
      (H:ℝ)*(1+120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12)) := by
  have hCp : 0 ≤ C := zero_le_one.trans hC
  have hlam1 : lam ≤ 1 := by linarith
  have hr1 : (1:ℝ) ≤ |(r:ℝ)| := by exact_mod_cast Int.one_le_abs hr
  have hc (h : ℤ) (hh : h ∈ robertSargosHOverlap H r) :
      ‖robertSargosZeroQSource f M h r‖ ≤
        1+120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12) := by
    have hi := (mem_robertSargosHOverlap H h r).mp hh
    have h₁ := Finset.mem_Ico.mp hi.1
    have h₂ := Finset.mem_Ico.mp hi.2
    have hh0 : 0 ≤ h := by omega
    have hhr0 : 0 ≤ h+r := by omega
    have hhR : (h:ℝ) < 2*H := by exact_mod_cast h₁.2
    have hhrR : (h:ℝ)+r < 2*H := by exact_mod_cast h₂.2
    have hslow := robertSargos_zero_q_slow_scale hCp hlam hlam1
      (show (0:ℝ) ≤ h by exact_mod_cast hh0)
      (show 0 ≤ (h:ℝ)+r by exact_mod_cast hhr0)
      (show (h:ℝ) ≤ lam^(-(2:ℝ)/13) by linarith)
      (show (h:ℝ)+r ≤ lam^(-(2:ℝ)/13) by linarith) hr1
    exact robertSargos_zero_q_source_bound f M h r hh0 hhr0 hr hC hlam
      (robertSargos_zero_q_curvature_scale hlam hsmall hrmax)
      (robertSargos_zero_q_block_length hlam hlam1 hr1 hM)
      hslow hf hlo hhi
  have he : robertSargosMixedCorrelation f M H 0 r =
      ∑ h ∈ robertSargosHOverlap H r, robertSargosZeroQSource f M h r := by
    simp only [robertSargosMixedCorrelation,robertSargosZeroQSource,Int.cast_zero,add_zero]
  rw [he]
  calc
    _ ≤ ∑ h ∈ robertSargosHOverlap H r, ‖robertSargosZeroQSource f M h r‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ robertSargosHOverlap H r,
        (1+120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12)) := Finset.sum_le_sum hc
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast robertSargos_h_overlap_card H r) (by positivity)

theorem robertSargos_zero_q_trimmed_correlation_bound
    (f : ℝ → ℝ) (M H : ℕ) (r : ℤ) {C lam : ℝ}
    (hr : r ≠ 0) (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hrmax : |(r:ℝ)| ≤ lam^(-(1:ℝ)/13))
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ‖robertSargosTrimmedCorrelation f M H 0 r‖ ≤
      (H:ℝ)*(1+120*C*(1+2*Real.pi*C)*M*(2*|(r:ℝ)| *lam)^((1:ℝ)/12))+
        2*H*|(r:ℝ)| := by
  calc
    _ = ‖robertSargosMixedCorrelation f M H 0 r -
        (robertSargosMixedCorrelation f M H 0 r-robertSargosTrimmedCorrelation f M H 0 r)‖ := by
      congr 1
      abel
    _ ≤ ‖robertSargosMixedCorrelation f M H 0 r‖+
        ‖robertSargosMixedCorrelation f M H 0 r-robertSargosTrimmedCorrelation f M H 0 r‖ :=
      norm_sub_le _ _
    _ ≤ _ := add_le_add
      (robertSargos_zero_q_mixed_correlation_bound f M H r hr hC hlam hsmall hM hH hrmax hf hlo hhi)
      (norm_robertSargos_correlation_endpoint_error f M H 0 r)

end TaoTrudgianYang2025
