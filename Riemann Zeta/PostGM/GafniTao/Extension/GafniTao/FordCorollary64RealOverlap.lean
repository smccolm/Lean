import GafniTao.FordLemma63Real
import GafniTao.FordCorollary64Overlap

/-!
# Corollary 6.4: exact real-scale overlap
-/

namespace GafniTao

noncomputable section

theorem fordLemma63WReal_eq_of_exact_scale
    {N k : ℕ} {P t : ℝ}
    (hk : 1 ≤ k) (hP : 1 ≤ P) (ht : 0 < t)
    (hscale : t * P ^ (k + 1) = (N : ℝ) ^ (k + 1)) :
    fordLemma63WReal N k P t =
      (2 : ℝ) ^ (k + 2) * P / (k : ℝ) ^ 2 + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hPR : 0 < P := zero_lt_one.trans_le hP
  unfold fordLemma63WReal
  field_simp [ne_of_gt hkR, ne_of_gt hPR, ne_of_gt ht]
  rw [← hscale]
  ring

theorem fordLemma63WReal_le_source_scale
    {N k : ℕ} {P t : ℝ}
    (hk : 4 ≤ k) (hP : 1 ≤ P) (ht : 0 < t)
    (hscale : t * P ^ (k + 1) = (N : ℝ) ^ (k + 1)) :
    fordLemma63WReal N k P t ≤ (2 : ℝ) ^ k * P := by
  rw [fordLemma63WReal_eq_of_exact_scale (by omega) hP ht hscale]
  let A : ℝ := (2 : ℝ) ^ (k - 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoef :
      (2 : ℝ) ^ (k + 2) / (k : ℝ) ^ 2 ≤ A := by
    simpa [A] using ford_two_pow_div_sq_le_half hk
  have hone : (1 : ℝ) ≤ A * P := by
    have hAone : (1 : ℝ) ≤ A := by
      dsimp [A]
      exact one_le_pow₀ (by norm_num)
    nlinarith
  have hfirst :
      (2 : ℝ) ^ (k + 2) * P / (k : ℝ) ^ 2 ≤ A * P := by
    calc
      (2 : ℝ) ^ (k + 2) * P / (k : ℝ) ^ 2 =
          ((2 : ℝ) ^ (k + 2) / (k : ℝ) ^ 2) * P := by ring
      _ ≤ A * P := by gcongr
  have hpow : (2 : ℝ) ^ k = 2 * A := by
    calc
      (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * A := by simp [A, mul_comm]
  rw [hpow]
  nlinarith

#print axioms fordLemma63WReal_eq_of_exact_scale
#print axioms fordLemma63WReal_le_source_scale

end

end GafniTao
