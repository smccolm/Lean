import TaoTrudgianYang2025.BourgainLevelElimination

/-!
# Exact relation between the two level-free comparison coefficients

The square-root coefficient squared is exactly the cardinality coefficient.
This retains every window, ceiling, logarithmic and fourth-moment factor.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_slice_sqrt_coefficient_sq {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) :
    (bourgainSliceSqrtCoefficient N L B C τ α ε 1)^2 =
      bourgainEliminatedCardCoefficient N L B C τ α ε := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH : 0 < N^(ε/8) := Real.rpow_pos_of_pos hNp _
  have hU : 0 < L+N^(ε/8)+1 := by linarith
  have hY : 0 ≤ C*(L+N^(ε/8)+1)^(1+ε) := by positivity
  have hK : 0 ≤ 2*N^(ε/8)*((2*Nat.ceil (N^(ε/8))+1 : ℕ) : ℝ) := by positivity
  have hα : (N^(-α))^2 = N^(-2*α) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  have hτ : (N^(τ/2))^2 = N^τ := by
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  unfold bourgainSliceSqrtCoefficient bourgainMassCoefficient
    bourgainEliminatedCardCoefficient
  simp only [div_pow, mul_pow, mul_one, Real.sq_sqrt hY,
    Real.sq_sqrt hK, hα, hτ]
  ring

/-- The exact nonnegative square root, including a zero fourth-moment constant. -/
theorem bourgain_slice_sqrt_coefficient_eq_sqrt {N L B C τ α ε : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) :
    bourgainSliceSqrtCoefficient N L B C τ α ε 1 =
      Real.sqrt (bourgainEliminatedCardCoefficient N L B C τ α ε) := by
  rw [← bourgain_slice_sqrt_coefficient_sq hN hL hC]
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZ := bourgainDifferenceLogLoss_pos hN τ
  have hb : 0 ≤ bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
    unfold bourgainSliceSqrtCoefficient bourgainMassCoefficient
    positivity
  exact (Real.sqrt_sq hb).symm

end TaoTrudgianYang2025
