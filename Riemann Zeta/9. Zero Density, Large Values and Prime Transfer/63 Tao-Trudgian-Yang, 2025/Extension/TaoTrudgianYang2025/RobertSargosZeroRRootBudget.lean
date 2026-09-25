import TaoTrudgianYang2025.SecondDerivativeScale

/-! Polynomial budgets for the actual zero-r row after the A-times-A coefficient. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem zero_r_positive_root_budget {H Q R lam : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hR : 0 < R) (hlam : 0 < lam)
    (hscale : H^5*Q*lam ≤ R^2) :
    H^2*Real.sqrt (4*H*lam)*Real.sqrt Q ≤ 2*R := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 2 ≠ 0)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hQ.le,
    Real.sq_sqrt (by positivity : 0 ≤ 4*H*lam)]
  nlinarith

theorem zero_r_inverse_root_budget {M H Q R lam : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hQ : 0 < Q) (hR : 0 < R) (hlam : 0 < lam)
    (hscale : H^3 ≤ M^2*R^2*Q*lam) :
    H^2*Real.sqrt Q/(Q*R*Real.sqrt (2*H*lam)) ≤ M := by
  apply (div_le_iff₀ (by positivity : 0 < Q*R*Real.sqrt (2*H*lam))).mpr
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 2 ≠ 0)).mp
  simp only [mul_pow,Real.sq_sqrt hQ.le,
    Real.sq_sqrt (by positivity : 0 ≤ 2*H*lam)]
  have hs := mul_le_mul_of_nonneg_right hscale (show 0 ≤ H*Q by positivity)
  nlinarith [show 0 ≤ M^2*R^2*Q^2*H*lam by positivity]

theorem zero_r_a_times_a_row_budget {M H Q R C lam : ℝ}
    (hM : 0 ≤ M) (hH : 0 < H) (hQ : 0 < Q) (hR : 0 < R)
    (hC : 1 ≤ C) (hlam : 0 < lam)
    (hdiag : H^2 ≤ M*R) (hpos : H^5*Q*lam ≤ R^2)
    (hinv : H^3 ≤ M^2*R^2*Q*lam) :
    (8*M*H/(Q*R))*
      (2*H*Q+24*C*M*H*Real.sqrt (4*H*lam)*Q*Real.sqrt Q+
        96*H*Real.sqrt Q/Real.sqrt (2*H*lam)) ≤ 1168*C*M^2 := by
  have hq0 : Q ≠ 0 := hQ.ne'
  have hr0 : R ≠ 0 := hR.ne'
  have hd : (8*M*H/(Q*R))*(2*H*Q) ≤ 16*M^2 := by
    have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hR).mpr hdiag)
      (show 0 ≤ 16*M by positivity)
    calc
      _ = (16*M)*(H^2/R) := by field_simp; ring
      _ ≤ (16*M)*M := hh
      _ = _ := by ring
  have hp : (8*M*H/(Q*R))*
      (24*C*M*H*Real.sqrt (4*H*lam)*Q*Real.sqrt Q) ≤ 384*C*M^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (zero_r_positive_root_budget hH hQ hR hlam hpos)
      (show 0 ≤ 192*C*M^2/R by positivity)
    calc
      _ = (192*C*M^2/R)*(H^2*Real.sqrt (4*H*lam)*Real.sqrt Q) := by
        field_simp
        ring
      _ ≤ (192*C*M^2/R)*(2*R) := hh
      _ = _ := by field_simp; ring
  have hi : (8*M*H/(Q*R))*(96*H*Real.sqrt Q/Real.sqrt (2*H*lam)) ≤ 768*M^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (zero_r_inverse_root_budget hM hH hQ hR hlam hinv)
      (show 0 ≤ 768*M by positivity)
    calc
      _ = (768*M)*(H^2*Real.sqrt Q/(Q*R*Real.sqrt (2*H*lam))) := by ring
      _ ≤ (768*M)*M := hh
      _ = _ := by ring
  have hc := mul_le_mul_of_nonneg_right hC (sq_nonneg M)
  rw [mul_add,mul_add]
  nlinarith

end TaoTrudgianYang2025
