import TaoTrudgianYang2025.BourgainBudgetLogarithm

/-!
# Taking logarithms of the finite two-term comparison

This module performs scalar algebra from the explicit finite comparison.
The subsequent source consumer supplies that inequality on its actual sets.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_logb_monomial {N A X R : ℝ}
    (hN : 1 < N) (hA : 0 < A) (hX : 0 < X) (hR : 0 < R) (p q r : ℝ) :
    Real.logb N (N^p/A*X^q*R^r) =
      p-Real.logb N A+q*Real.logb N X+r*Real.logb N R := by
  have hNp : 0 < N := zero_lt_one.trans hN
  rw [Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hR _).ne',
    Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hX _).ne',
    Real.logb_div (Real.rpow_pos_of_pos hNp _).ne' hA.ne',
    Real.logb_rpow hNp hN.ne', Real.logb_rpow_eq_mul_logb_of_pos hX,
    Real.logb_rpow_eq_mul_logb_of_pos hR]

theorem bourgain_mixed_budget_log_bound {N T R X K τ : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hX : 0 < X) (hK : 0 < K)
    (hcap : T ≤ N^τ) (a : ℝ) :
    Real.logb N (K*N^a*
      (Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X))) ≤
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τ (Real.logb N X)/2 := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hBR := bourgainSecondBudget_pos hNp hT hR
  have hBX := bourgainSecondBudget_pos hNp hT hX
  have hRlog := bourgain_budget_log_bound hN hT hR hcap
  have hXlog := bourgain_budget_log_bound hN hT hX hcap
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul hK.ne' (Real.rpow_pos_of_pos hNp _).ne',
    Real.logb_rpow hNp hN.ne',
    Real.logb_mul (Real.sqrt_pos.mpr hBR).ne' (Real.sqrt_pos.mpr hBX).ne',
    Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) hK.ne']
  simp only [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hBR,
    Real.logb_rpow_eq_mul_logb_of_pos hBX]
  linarith

/-- Both positive summands of the actual finite comparison give their
logarithmic inequalities, retaining every explicit loss and fixed multiplier. -/
theorem bourgain_finite_comparison_logarithm {N T R X K G σ τ δ α χ E a : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hX : 0 < X)
    (hK : 0 < K) (hG : 0 < G) (hcap : T ≤ N^τ)
    (hcomp : N^(2*σ-2*δ)*
      (N^(-2*α-E)/G*X*R+
        N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt X*R^(3/2 : ℝ)) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X))) :
    max (-2*α+2*σ+Real.logb N X+Real.logb N R-E-2*δ-Real.logb N G)
      (-α-χ/2+2*σ+Real.logb N X/2+3*Real.logb N R/2-E/2-2*δ-Real.logb N (2*G)/2) <
      Real.logb N (3*K)+a+
        heathBrownDoubleZetaExponent τ (Real.logb N R)/2+
        heathBrownDoubleZetaExponent τ (Real.logb N X)/2 := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hfirst : N^(2*σ-2*δ)*(N^(-2*α-E)/G*X*R) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X)) :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
      (Real.rpow_nonneg hNp.le _)).trans_lt hcomp
  have hsecond : N^(2*σ-2*δ)*
      (N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt X*R^(3/2 : ℝ)) <
      K*N^a*(Real.sqrt (bourgainSecondBudget N T R)*Real.sqrt (bourgainSecondBudget N T X)) :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
      (Real.rpow_nonneg hNp.le _)).trans_lt hcomp
  have hlog₁ := Real.logb_lt_logb hN (by positivity) hfirst
  have hlog₂ := Real.logb_lt_logb hN (by positivity) hsecond
  have heq₁ : N^(2*σ-2*δ)*(N^(-2*α-E)/G*X*R) =
      N^((2*σ-2*δ)+(-2*α-E))/G*X^(1 : ℝ)*R^(1 : ℝ) := by
    rw [Real.rpow_add hNp, Real.rpow_one, Real.rpow_one]
    ring
  have heq₂ : N^(2*σ-2*δ)*
      (N^(-α-E/2-χ/2)/Real.sqrt (2*G)*Real.sqrt X*R^(3/2 : ℝ)) =
      N^((2*σ-2*δ)+(-α-E/2-χ/2))/Real.sqrt (2*G)*X^(1/2 : ℝ)*R^(3/2 : ℝ) := by
    rw [Real.rpow_add hNp]
    simp only [Real.sqrt_eq_rpow]
    ring
  rw [heq₁, bourgain_logb_monomial hN hG hX hR] at hlog₁
  rw [heq₂, bourgain_logb_monomial hN (Real.sqrt_pos.mpr (by positivity)) hX hR] at hlog₂
  rw [Real.sqrt_eq_rpow,
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity : 0 < 2*G)] at hlog₂
  have hupper := bourgain_mixed_budget_log_bound hN hT hR hX hK hcap a
  exact max_lt (by linarith) (by linarith)

end TaoTrudgianYang2025
