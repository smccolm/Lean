import TaoTrudgianYang2025.RobertSargosShiftedCorrelation
import TaoTrudgianYang2025.RobertSargosWeightedBoundary

/-! The common-interval shift error with both exact triangular weights. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_signed_triangular_double_constant (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (C : ℝ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*C) = C*Q*R := by
  calc
    _ = C*(∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, (1-|(q:ℝ)|/Q))*
        (∑ r ∈ Finset.Ioo (-(R:ℤ)) R, (1-|(r:ℝ)|/R)) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by rw [sum_signed_triangular_weights Q hQ,sum_signed_triangular_weights R hR]

theorem robertSargos_weighted_shift_error (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hN : 0 < N) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H q r).re) ≤
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*(robertSargosShiftedCorrelation f M H Q N q r).re) +
      (H:ℝ)*(4*(H:ℝ)+4*Q+2*N)*Q*R := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
          ((robertSargosShiftedCorrelation f M H Q N q r).re+
            (H:ℝ)*(4*(H:ℝ)+4*Q+2*N)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg
        (signed_triangular_weight_nonneg hQ hq) (signed_triangular_weight_nonneg hR hr))
      have hn := norm_robertSargos_trimmed_shift_error f M H Q N q r hN hq
      have he := Complex.re_le_norm
        (robertSargosTrimmedCorrelation f M H q r-robertSargosShiftedCorrelation f M H Q N q r)
      rw [Complex.sub_re] at he
      linarith
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,
        sum_signed_triangular_double_constant Q R hQ hR]
      ring

theorem robertSargos_shifted_a_times_a (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hN : 0 < N) (hQM : Q ≤ M) (hRH : R ≤ 2*H) :
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      (8*(M:ℝ)*H/((Q:ℝ)*R))*
        (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            (robertSargosShiftedCorrelation f M H Q N q r).re) +
      16*(M:ℝ)*(H:ℝ)^2*R+
      8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+4*Q+2*N) := by
  have hs := robertSargos_trimmed_a_times_a f M H Q R hQ hR hQM hRH
  have he := mul_le_mul_of_nonneg_left (robertSargos_weighted_shift_error f M H Q R N hQ hR hN)
    (show 0 ≤ 8*(M:ℝ)*H/((Q:ℝ)*R) by positivity)
  have hcancel : (8*(M:ℝ)*H/((Q:ℝ)*R))*
      ((H:ℝ)*(4*(H:ℝ)+4*Q+2*N)*Q*R) =
      8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+4*Q+2*N) := by
    have hq : (Q:ℝ) ≠ 0 := by positivity
    have hr : (R:ℝ) ≠ 0 := by positivity
    field_simp
  rw [mul_add,hcancel] at he
  calc
    _ ≤ ((8*(M:ℝ)*H/((Q:ℝ)*R))*
        (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            (robertSargosShiftedCorrelation f M H Q N q r).re)+
          8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+4*Q+2*N))+
          16*(M:ℝ)*(H:ℝ)^2*R :=
      hs.trans (add_le_add_left he _)
    _ = _ := by ring

end TaoTrudgianYang2025
