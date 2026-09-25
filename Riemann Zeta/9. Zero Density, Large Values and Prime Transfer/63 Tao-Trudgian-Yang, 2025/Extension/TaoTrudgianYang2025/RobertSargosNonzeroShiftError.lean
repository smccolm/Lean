import TaoTrudgianYang2025.RobertSargosWeightedZeroSplit
import TaoTrudgianYang2025.RobertSargosWeightedShift

/-! Common-interval shifting after both coordinate axes have been excluded. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_nonzero_signed_triangular_constant_le (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
      ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*C) ≤ C*Q*R := by
  calc
    _ ≤ ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
        ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*C := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro r hr _
      exact mul_nonneg (mul_nonneg
        (signed_triangular_weight_nonneg hQ (Finset.mem_erase.mp hq).2)
        (signed_triangular_weight_nonneg hR hr)) hC
    _ ≤ ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q,
        ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro q hq _
      apply Finset.sum_nonneg
      intro r hr
      exact mul_nonneg (mul_nonneg
        (signed_triangular_weight_nonneg hQ hq)
        (signed_triangular_weight_nonneg hR hr)) hC
    _ = _ := sum_signed_triangular_double_constant Q R hQ hR C

theorem robertSargos_nonzero_weighted_shift_error (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hN : 0 < N) :
    robertSargosNonzeroShiftSum f M H Q R ≤
      (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
        ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosShiftedCorrelation f M H Q N q r).re)+
        (H:ℝ)*(4*(H:ℝ)+4*Q+2*N)*Q*R := by
  unfold robertSargosNonzeroShiftSum
  calc
    _ ≤ ∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0,
        ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            ((robertSargosShiftedCorrelation f M H Q N q r).re+
              (H:ℝ)*(4*(H:ℝ)+4*Q+2*N)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqm := (Finset.mem_erase.mp hq).2
      have hrm := (Finset.mem_erase.mp hr).2
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg
        (signed_triangular_weight_nonneg hQ hqm) (signed_triangular_weight_nonneg hR hrm))
      have hn := norm_robertSargos_trimmed_shift_error f M H Q N q r hN hqm
      have he := Complex.re_le_norm
        (robertSargosTrimmedCorrelation f M H q r-robertSargosShiftedCorrelation f M H Q N q r)
      rw [Complex.sub_re] at he
      linarith
    _ ≤ _ := by
      have hb := sum_nonzero_signed_triangular_constant_le Q R hQ hR
        ((H:ℝ)*(4*(H:ℝ)+4*Q+2*N)) (by positivity)
      simp only [mul_add,Finset.sum_add_distrib] at hb ⊢
      exact add_le_add_right hb _

end TaoTrudgianYang2025
