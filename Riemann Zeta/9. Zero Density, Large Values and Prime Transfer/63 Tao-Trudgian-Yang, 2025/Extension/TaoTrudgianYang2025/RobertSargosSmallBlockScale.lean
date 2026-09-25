import TaoTrudgianYang2025.ThirdDerivativeRpowScale

/-! Explicit polynomial budgets sufficient for the source small-block branch. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sixth_root_pow_six {x : ℝ} (hx : 0 ≤ x) :
    (x^((1:ℝ)/6))^6 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem small_block_sixth_root {H lam : ℝ}
    (hH : 0 ≤ H) (hlam : 0 ≤ lam) (hscale : H^7*lam ≤ 1) :
    H*(4*H*lam)^((1:ℝ)/6) ≤ 2 := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : 6 ≠ 0)).mp
  rw [mul_pow,sixth_root_pow_six (by positivity)]
  nlinarith

theorem small_block_inverse_sixth_root {M H lam : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hlam : 0 < lam) (hscale : H^5 ≤ M^3*lam) :
    H*Real.sqrt M*(2*H*lam)^(-(1:ℝ)/6) ≤ M := by
  have ht : 0 < (2*H*lam)^((1:ℝ)/6) := by positivity
  have hsqrt : (Real.sqrt M)^6 = M^3 := by
    calc
      _ = ((Real.sqrt M)^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hM]
  have hp : H*Real.sqrt M ≤ M*(2*H*lam)^((1:ℝ)/6) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 6 ≠ 0)).mp
    rw [mul_pow,mul_pow,hsqrt,sixth_root_pow_six (by positivity)]
    calc
      H^6*M^3 = H^5*(H*M^3) := by ring
      _ ≤ (M^3*lam)*(H*M^3) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ ≤ M^6*(2*H*lam) := by nlinarith [show 0 ≤ H*M^6*lam by positivity]
  rw [show -(1:ℝ)/6 = -((1:ℝ)/6) by ring,Real.rpow_neg (by positivity),
    ← div_eq_mul_inv]
  exact (div_le_iff₀ ht).mpr hp

theorem small_block_third_derivative_budget {M H C lam : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hHM : H ≤ M) (hC : 1 ≤ C) (hlam : 0 < lam)
    (hfirst : H^7*lam ≤ 1) (hsecond : H^5 ≤ M^3*lam) :
    H*(1+20*C*(M*(4*H*lam)^((1:ℝ)/6)+
      Real.sqrt M*(2*H*lam)^(-(1:ℝ)/6))) ≤ 61*C*M := by
  have h1 := mul_le_mul_of_nonneg_left (small_block_sixth_root hH.le hlam.le hfirst) hM
  have h2 := small_block_inverse_sixth_root hM hH hlam hsecond
  have h3 := mul_le_mul_of_nonneg_right hC hM
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ 20*C by positivity)
  nlinarith

end TaoTrudgianYang2025
