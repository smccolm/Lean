import TaoTrudgianYang2025.SquareRootShiftSums

/-! Summed explicit second-derivative bounds for the third-derivative method. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_third_derivative_correlation_majorant
    (N H : ℕ) {C μ : ℝ} (hC : 0 ≤ C) (hμ : 0 < μ) :
    (∑ r ∈ Finset.Icc 1 (H-1),
      12*(C*N*Real.sqrt ((r:ℝ)*μ)+2/Real.sqrt ((r:ℝ)*μ))) ≤
        12*(C*N*Real.sqrt μ*((H:ℝ)*Real.sqrt H)+4*Real.sqrt H/Real.sqrt μ) := by
  have he (r : ℕ) :
      12*(C*N*Real.sqrt ((r:ℝ)*μ)+2/Real.sqrt ((r:ℝ)*μ)) =
        12*(C*N*Real.sqrt μ*Real.sqrt r+(2/Real.sqrt μ)*(1/Real.sqrt r)) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg r)]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left (sum_shift_sqrt_le H)
    (show 0 ≤ C*N*Real.sqrt μ by positivity)
  have hi := mul_le_mul_of_nonneg_left (sum_shift_inverse_sqrt_le H)
    (show 0 ≤ 2/Real.sqrt μ by positivity)
  calc
    _ ≤ 12*(C*N*Real.sqrt μ*((H:ℝ)*Real.sqrt H)+
        (2/Real.sqrt μ)*(2*Real.sqrt H)) :=
      mul_le_mul_of_nonneg_left (add_le_add hs hi) (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025
