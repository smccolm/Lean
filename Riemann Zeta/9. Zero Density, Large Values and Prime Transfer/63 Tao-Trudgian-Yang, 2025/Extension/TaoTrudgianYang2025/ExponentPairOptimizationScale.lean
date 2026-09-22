import TaoTrudgianYang2025.ExponentPairDifferencingBound

/-! The real optimization scale is linked to the actual physical parameters. -/

noncomputable section

namespace TaoTrudgianYang2025

def aProcessOptimizationScale (q p T N : ℝ) : ℝ :=
  (T/N)^(-q/(q+1))*N^((1-p+q)/(q+1))

theorem aProcessOptimizationScale_pos {q p T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) :
    0 < aProcessOptimizationScale q p T N := by
  unfold aProcessOptimizationScale
  positivity

theorem aProcessOptimizationScale_le {q p T N : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hN : 1 ≤ N) (hNT : N ≤ T) :
    aProcessOptimizationScale q p T N ≤ N := by
  have hNpos := zero_lt_one.trans_le hN
  have hratio : 1 ≤ T/N := (le_div_iff₀ hNpos).mpr (by simpa using hNT)
  have hden : 0 < q+1 := by linarith
  have h₁ : (T/N)^(-q/(q+1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hratio (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le)
  have h₂ : N^((1-p+q)/(q+1)) ≤ N := by
    calc
      _ ≤ N^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        ((div_le_iff₀ hden).mpr (by linarith))
      _ = N := Real.rpow_one _
  unfold aProcessOptimizationScale
  have hp₂ : 0 ≤ N^((1-p+q)/(q+1)) := by positivity
  exact (mul_le_mul_of_nonneg_right h₁ hp₂).trans (by simpa using h₂)

theorem aProcessOptimizationScale_log {q p T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) :
    Real.log (aProcessOptimizationScale q p T N) =
      (-q/(q+1))*Real.log (T/N)+((1-p+q)/(q+1))*Real.log N := by
  have hratio : 0 < T/N := by positivity
  rw [aProcessOptimizationScale,Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hratio,Real.log_rpow hN]

theorem aProcessOptimizationScale_balance {q p T N : ℝ}
    (hq : 0 ≤ q) (hT : 0 < T) (hN : 0 < N) :
    ((T/N^2)^q*N^p)*(aProcessOptimizationScale q p T N)^(q+1) = N := by
  have hden : q+1 ≠ 0 := by linarith
  have hratio : 0 < T/N := by positivity
  have hR := aProcessOptimizationScale_pos (q := q) (p := p) hT hN
  have hM : 0 < (T/N^2)^q*N^p := by positivity
  apply Real.log_injOn_pos (mul_pos hM (Real.rpow_pos_of_pos hR _)) hN
  rw [Real.log_mul hM.ne' (Real.rpow_pos_of_pos hR _).ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity),Real.log_rpow hN,Real.log_rpow hR,
    aProcessOptimizationScale_log hT hN]
  rw [show T/N^2 = (T/N)/N by ring,Real.log_div hratio.ne' hN.ne']
  field_simp
  ring

theorem aProcessOptimizationScale_cost {q p T N : ℝ}
    (hq : 0 ≤ q) (hT : 0 < T) (hN : 0 < N) :
    N^2/aProcessOptimizationScale q p T N =
      (T/N)^(q/(q+1))*N^(1+p/(q+1)) := by
  have hden : q+1 ≠ 0 := by linarith
  have hratio : 0 < T/N := by positivity
  have hR := aProcessOptimizationScale_pos (q := q) (p := p) hT hN
  apply Real.log_injOn_pos (div_pos (sq_pos_of_pos hN) hR)
    (show 0 < (T/N)^(q/(q+1))*N^(1+p/(q+1)) by positivity)
  rw [Real.log_div (by positivity) hR.ne',Real.log_pow,
    aProcessOptimizationScale_log hT hN,
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hratio,Real.log_rpow hN]
  field_simp
  ring

end TaoTrudgianYang2025
