import TaoTrudgianYang2025.RobertSargosCorrelationBoundary
import TaoTrudgianYang2025.RobertSargosZeroRSignedBound

/-! The signed zero-r bound on the actual h-intersection in the A-times-A source. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_trimmed_correlation_bound
    (f : ℝ → ℝ) (M H : ℕ) (q : ℤ) {C lam : ℝ}
    (hC : 0 ≤ C) (hH : 0 < H) (hq : q ≠ 0) (hlam : 0 < lam)
    (hscale : 4*(H:ℝ)*|(q:ℝ)| *lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosTrimmedCorrelation f M H q 0‖ ≤
      (H:ℝ)*(1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
        2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam))) := by
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hqp : 0 < |(q:ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hc (h : ℤ) (hh : h ∈ robertSargosHOverlap H 0) :
      ‖robertSargosZeroRSource f M h q‖ ≤
        1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
          2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam)) := by
    have hi := ((mem_robertSargosHOverlap H h 0).mp hh).1
    have hii := Finset.mem_Ico.mp hi
    have hHh : (H:ℝ) ≤ h := by exact_mod_cast hii.1
    have hhH : (h:ℝ) < 2*H := by exact_mod_cast hii.2
    have hhr : (0:ℝ) < h := hHr.trans_le hHh
    have hloScale : 2*(H:ℝ)*|(q:ℝ)| *lam ≤ 2*(h:ℝ)*|(q:ℝ)| *lam := by
      nlinarith [mul_pos hqp hlam]
    have hhiScale : 2*(h:ℝ)*|(q:ℝ)| *lam ≤ 4*(H:ℝ)*|(q:ℝ)| *lam := by
      nlinarith [mul_pos hqp hlam]
    have hp := robertSargos_zero_r_source_bound f M h q hC (by exact_mod_cast hhr)
      hq hlam (hhiScale.trans hscale) hf hlo hhi
    have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhiScale)
      (show 0 ≤ C*M by positivity)
    have hi' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
      (by positivity : 0 < Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam))
      (Real.sqrt_le_sqrt hloScale)
    linarith
  have he : robertSargosTrimmedCorrelation f M H q 0 =
      ∑ h ∈ robertSargosHOverlap H 0, robertSargosZeroRSource f M h q := by
    simp only [robertSargosTrimmedCorrelation,robertSargosZeroRSource,Int.cast_zero,add_zero]
  rw [he]
  calc
    _ ≤ ∑ h ∈ robertSargosHOverlap H 0, ‖robertSargosZeroRSource f M h q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _h ∈ robertSargosHOverlap H 0,
        (1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
          2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam))) := Finset.sum_le_sum hc
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast robertSargos_h_overlap_card H 0) (by positivity)

end TaoTrudgianYang2025
