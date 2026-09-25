import TaoTrudgianYang2025.RobertSargosShiftReorder

/-! The norm is taken only after the inner q,h,n sum has been assembled. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_weighted_shifted_re (f : ℝ → ℝ) (M H Q R N : ℕ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
        (robertSargosShiftedCorrelation f M H Q N q r).re) =
      (N:ℝ)⁻¹*∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        (1-|(r:ℝ)|/R)*
          ∑ m ∈ robertSargosCommonMInterval M H Q N,
            (robertSargosShiftedTriple f H Q N r m).re := by
  have he := congrArg Complex.re (robertSargos_weighted_shifted_reorder f M H Q R N)
  have hi : (N:ℂ)⁻¹ = (((N:ℝ)⁻¹:ℝ):ℂ) := by
    simp only [Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [hi] at he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using he

theorem robertSargos_weighted_shifted_re_le (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hR : 0 < R) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
        (robertSargosShiftedCorrelation f M H Q N q r).re) ≤
      (N:ℝ)⁻¹*∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        ∑ m ∈ robertSargosCommonMInterval M H Q N,
          ‖robertSargosShiftedTriple f H Q N r m‖ := by
  rw [robertSargos_weighted_shifted_re]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hw : 1-|(r:ℝ)|/R ≤ 1 := sub_le_self _ (by positivity)
  exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    (signed_triangular_weight_nonneg hR hr)).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hw
        (norm_nonneg (robertSargosShiftedTriple f H Q N r m))))

theorem robertSargos_shifted_triple_a_times_a (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hN : 0 < N) (hQM : Q ≤ M) (hRH : R ≤ 2*H) :
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      (8*(M:ℝ)*H/((Q:ℝ)*R*N))*
        (∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          ∑ m ∈ robertSargosCommonMInterval M H Q N,
            ‖robertSargosShiftedTriple f H Q N r m‖) +
      16*(M:ℝ)*(H:ℝ)^2*R+
      8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+4*Q+2*N) := by
  have hs := robertSargos_shifted_a_times_a f M H Q R N hQ hR hN hQM hRH
  have he := mul_le_mul_of_nonneg_left
    (robertSargos_weighted_shifted_re_le f M H Q R N hR)
    (show 0 ≤ 8*(M:ℝ)*H/((Q:ℝ)*R) by positivity)
  have halg (B : ℝ) : (8*(M:ℝ)*H/((Q:ℝ)*R))*((N:ℝ)⁻¹*B) =
      (8*(M:ℝ)*H/((Q:ℝ)*R*N))*B := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [halg] at he
  exact hs.trans (add_le_add_left (add_le_add_left he _) _)

end TaoTrudgianYang2025
