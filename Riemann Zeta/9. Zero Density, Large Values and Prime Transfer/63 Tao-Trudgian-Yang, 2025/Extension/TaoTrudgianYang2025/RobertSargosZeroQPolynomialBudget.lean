import TaoTrudgianYang2025.ThirteenthRootScales

/-! Polynomial budgets for the zero-q column at the physical thirteenth-root scales. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem zero_q_twelfth_root_budget {T R lam : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hRmax : R ≤ T) (hlam : 0 < lam)
    (hscale : T^13*lam = 1) :
    T*(2*R*lam)^((1:ℝ)/12) ≤ 2 := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : 12 ≠ 0)).mp
  rw [mul_pow]
  have hp : ((2*R*lam)^((1:ℝ)/12))^12 = 2*R*lam := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 2*R*lam)]
    norm_num
  rw [hp]
  have hm := mul_le_mul_of_nonneg_left hRmax (show 0 ≤ 2*T^12*lam by positivity)
  nlinarith

theorem zero_q_physical_polynomial_budgets {T M H Q R lam : ℝ}
    (hT : 2 ≤ T) (hM : T^8 ≤ M) (hH : 0 ≤ H) (hHmax : H ≤ T^2/2)
    (hQ : T^3/2 ≤ Q) (hR : 0 ≤ R) (hRmax : R ≤ T) (hlam : 0 < lam)
    (hscale : T^13*lam = 1) :
    H^2 ≤ M*Q/2 ∧ H^2*R ≤ M*Q/2 ∧ H^2*(2*R*lam)^((1:ℝ)/12) ≤ Q := by
  have hT1 : 1 ≤ T := by linarith
  have hQ0 : 0 ≤ Q := (show 0 ≤ T^3/2 by positivity).trans hQ
  have hM0 : 0 ≤ M := (pow_nonneg (by linarith) 8).trans hM
  have hs := mul_self_le_mul_self hH hHmax
  have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ T/2 by linarith)
  have hHQ : H^2 ≤ T*Q/2 := by nlinarith
  have hTM : T ≤ M := (le_self_pow₀ hT1 (by norm_num : 8 ≠ 0)).trans hM
  have hT2M : T^2 ≤ M := by
    have h6 : 1 ≤ T^6 := one_le_pow₀ hT1
    nlinarith [mul_le_mul_of_nonneg_left h6 (sq_nonneg T)]
  have hfirst := mul_le_mul_of_nonneg_right hTM hQ0
  have hsecond := mul_le_mul hHQ hRmax hR (show 0 ≤ T*Q/2 by positivity)
  have hsecond' := mul_le_mul_of_nonneg_right hT2M hQ0
  have hroot := zero_q_twelfth_root_budget (show 0 ≤ T by linarith) hR hRmax hlam hscale
  have hx : 0 ≤ (2*R*lam)^((1:ℝ)/12) := Real.rpow_nonneg (by positivity) _
  have hxH := mul_le_mul_of_nonneg_right hHQ hx
  have hxQ := mul_le_mul_of_nonneg_right hroot hQ0
  constructor
  · nlinarith
  constructor <;> nlinarith

end TaoTrudgianYang2025
