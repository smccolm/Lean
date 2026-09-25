import TaoTrudgianYang2025.RobertSargosNonzeroShiftReorder

/-! The norm is taken only after the inner q,h,n sum has been assembled. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_nonzero_weighted_shifted_re (f : ℝ → ℝ) (M H Q R N : ℕ) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
        (robertSargosShiftedCorrelation f M H Q N q r).re) =
      (N:ℝ)⁻¹*∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        (1-|(r:ℝ)|/R)*
          ∑ m ∈ robertSargosCommonMInterval M H Q N,
            (robertSargosNonzeroShiftedTriple f H Q N r m).re := by
  have he := congrArg Complex.re (robertSargos_nonzero_weighted_shifted_reorder f M H Q R N)
  have hi : (N:ℂ)⁻¹ = (((N:ℝ)⁻¹:ℝ):ℂ) := by
    simp only [Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [hi] at he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using he

theorem robertSargos_nonzero_weighted_shifted_re_le (f : ℝ → ℝ) (M H Q R N : ℕ)
    (hR : 0 < R) :
    (∑ q ∈ (Finset.Ioo (-(Q:ℤ)) Q).erase 0, ∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
        (robertSargosShiftedCorrelation f M H Q N q r).re) ≤
      (N:ℝ)⁻¹*∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
        ∑ m ∈ robertSargosCommonMInterval M H Q N,
          ‖robertSargosNonzeroShiftedTriple f H Q N r m‖ := by
  rw [robertSargos_nonzero_weighted_shifted_re]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hw : 1-|(r:ℝ)|/R ≤ 1 := sub_le_self _ (by positivity)
  exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    (signed_triangular_weight_nonneg hR (Finset.mem_erase.mp hr).2)).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hw
        (norm_nonneg (robertSargosNonzeroShiftedTriple f H Q N r m))))

end TaoTrudgianYang2025
