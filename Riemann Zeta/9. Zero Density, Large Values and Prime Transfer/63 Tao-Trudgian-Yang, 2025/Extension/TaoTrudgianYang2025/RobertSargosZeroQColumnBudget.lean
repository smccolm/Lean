import TaoTrudgianYang2025.RobertSargosZeroQPolynomialBudget

/-! The zero-q column after the actual A-times-A prefactor. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem zero_q_a_times_a_column_budget {M H Q R C lam : ℝ}
    (hM : 0 ≤ M) (hQ : 0 < Q) (hR : 0 < R) (hC : 1 ≤ C)
    (hdiag : H^2 ≤ M*Q/2) (herr : H^2*R ≤ M*Q/2)
    (hroot : H^2*(2*R*lam)^((1:ℝ)/12) ≤ Q) :
    (8*M*H/(Q*R))*
      (2*R*(H*(1+120*C*(1+2*Real.pi*C)*M*(2*R*lam)^((1:ℝ)/12))+2*H*R)) ≤
        1944*C*(1+2*Real.pi*C)*M^2 := by
  have hq0 : Q ≠ 0 := hQ.ne'
  have hr0 : R ≠ 0 := hR.ne'
  have hCp : 0 ≤ C := zero_le_one.trans hC
  let F := C*(1+2*Real.pi*C)
  have hF : 1 ≤ F := by
    have hf : 1 ≤ 1+2*Real.pi*C := by
      have hp : 0 ≤ 2*Real.pi*C := by positivity
      linarith
    exact hC.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hCp)
  have hd : (16*M/Q)*H^2 ≤ 8*M^2 := by
    have hh := mul_le_mul_of_nonneg_left hdiag (show 0 ≤ 16*M/Q by positivity)
    apply hh.trans_eq
    field_simp
    ring
  have he : (32*M/Q)*(H^2*R) ≤ 16*M^2 := by
    have hh := mul_le_mul_of_nonneg_left herr (show 0 ≤ 32*M/Q by positivity)
    apply hh.trans_eq
    field_simp
    ring
  have hm : (1920*F*M^2/Q)*(H^2*(2*R*lam)^((1:ℝ)/12)) ≤ 1920*F*M^2 := by
    have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 1920*F*M^2/Q by positivity)
    apply hh.trans_eq
    field_simp
  have hsum : (8*M*H/(Q*R))*
      (2*R*(H*(1+120*C*(1+2*Real.pi*C)*M*(2*R*lam)^((1:ℝ)/12))+2*H*R)) =
      (16*M/Q)*H^2+(1920*F*M^2/Q)*(H^2*(2*R*lam)^((1:ℝ)/12))+
        (32*M/Q)*(H^2*R) := by
    dsimp [F]
    field_simp
    ring
  rw [hsum]
  have hFM := mul_le_mul_of_nonneg_right hF (sq_nonneg M)
  dsimp only [F] at hm hFM ⊢
  nlinarith

end TaoTrudgianYang2025
