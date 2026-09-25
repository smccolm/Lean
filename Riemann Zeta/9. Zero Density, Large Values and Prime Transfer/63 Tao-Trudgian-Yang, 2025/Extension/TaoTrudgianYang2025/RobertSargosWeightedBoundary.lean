import TaoTrudgianYang2025.RobertSargosCorrelationBoundary
import TaoTrudgianYang2025.TriangularShiftBounds

/-! The source A-times-A estimate after the r-dependent endpoint replacement,
including its explicit total error. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem signed_triangular_double_endpoint_error (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(C*|(r:ℝ)|)) ≤ C*Q*(R:ℝ)^2 := by
  calc
    _ = (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, (1-|(q:ℝ)|/Q))*
        (C*(∑ r ∈ Finset.Ioo (-(R:ℤ)) R, (1-|(r:ℝ)|/R)*|(r:ℝ)|)) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ (Q:ℝ)*(C*(R:ℝ)^2) := by
      rw [sum_signed_triangular_weights Q hQ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (signed_triangular_first_moment R hR) hC)
        (Nat.cast_nonneg Q)
    _ = _ := by ring

theorem robertSargos_weighted_endpoint_error (f : ℝ → ℝ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosMixedCorrelation f M H q r).re) ≤
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H q r).re) +
      2*(H:ℝ)*Q*(R:ℝ)^2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
          ((robertSargosTrimmedCorrelation f M H q r).re+2*(H:ℝ)*|(r:ℝ)|) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg
        (signed_triangular_weight_nonneg hQ hq) (signed_triangular_weight_nonneg hR hr))
      have hn := norm_robertSargos_correlation_endpoint_error f M H q r
      have he := Complex.re_le_norm
        (robertSargosMixedCorrelation f M H q r-robertSargosTrimmedCorrelation f M H q r)
      rw [Complex.sub_re] at he
      linarith
    _ ≤ _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      exact add_le_add_right
        (signed_triangular_double_endpoint_error Q R hQ hR (2*(H:ℝ)) (by positivity)) _

theorem robertSargos_trimmed_a_times_a (f : ℝ → ℝ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hQM : Q ≤ M) (hRH : R ≤ 2*H) :
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      (8*(M:ℝ)*H/((Q:ℝ)*R))*
        (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            (robertSargosTrimmedCorrelation f M H q r).re) +
      16*(M:ℝ)*(H:ℝ)^2*R := by
  have hs := robertSargos_symmetric_a_times_a f M H Q R hQ hR hQM hRH
  have he := mul_le_mul_of_nonneg_left (robertSargos_weighted_endpoint_error f M H Q R hQ hR)
    (show 0 ≤ 8*(M:ℝ)*H/((Q:ℝ)*R) by positivity)
  have hcancel : (8*(M:ℝ)*H/((Q:ℝ)*R))*(2*(H:ℝ)*Q*(R:ℝ)^2) =
      16*(M:ℝ)*(H:ℝ)^2*R := by
    have hq : (Q:ℝ) ≠ 0 := by positivity
    have hr : (R:ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [mul_add,hcancel] at he
  exact hs.trans he

end TaoTrudgianYang2025
