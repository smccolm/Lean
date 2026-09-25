import TaoTrudgianYang2025.RobertSargosZeroRBlock
import TaoTrudgianYang2025.RobertSargosZeroRMajorant

/-! The actual nonzero-q, zero-r triangular row in the source A-times-A inequality. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_weighted_row_bound
    (f : ℝ → ℝ) (M H Q : ℕ) {C lam : ℝ}
    (hC : 0 ≤ C) (hH : 0 < H) (hQ : 0 < Q) (hlam : 0 < lam)
    (hscale : 4*(H:ℝ)*Q*lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
      (1-|(q:ℝ)|/Q)*(robertSargosTrimmedCorrelation f M H q 0).re) ≤
      2*(H:ℝ)*Q+24*C*M*H*Real.sqrt (4*(H:ℝ)*lam)*Q*Real.sqrt Q+
        96*H*Real.sqrt Q/Real.sqrt (2*(H:ℝ)*lam) := by
  let B : ℤ → ℝ := fun q =>
    (H:ℝ)*(1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
      2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam)))
  have hpoint (q : ℤ) (hq : q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0) :
      (1-|(q:ℝ)|/Q)*(robertSargosTrimmedCorrelation f M H q 0).re ≤ B q := by
    have hmem := Finset.mem_erase.mp hq
    have habs := signed_shift_abs_le hmem.2
    have hs : 4*(H:ℝ)*|(q:ℝ)| *lam ≤ 1 := by
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left habs (show 0 ≤ 4*(H:ℝ) by positivity)) hlam.le
      exact hb.trans hscale
    have hb := robertSargos_zero_r_trimmed_correlation_bound f M H q
      hC hH hmem.1 hlam hs hf hlo hhi
    have hw0 := signed_triangular_weight_nonneg hQ hmem.2
    have hw1 : 1-|(q:ℝ)|/Q ≤ 1 := by
      have hn : 0 ≤ |(q:ℝ)|/Q := by positivity
      linarith
    calc
      _ ≤ (1-|(q:ℝ)|/Q)*‖robertSargosTrimmedCorrelation f M H q 0‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hw0
      _ ≤ ‖robertSargosTrimmedCorrelation f M H q 0‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
      _ ≤ B q := hb
  calc
    _ ≤ ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, B q := Finset.sum_le_sum hpoint
    _ ≤ ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, B q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (by intro q _ _; dsimp [B]; positivity)
    _ ≤ _ := sum_robertSargos_zero_r_majorant M H Q hC hlam.le

end TaoTrudgianYang2025
