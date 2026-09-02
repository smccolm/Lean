import GafniTao.FordCorollary64Scale

/-!
# Ford Corollary 6.4: the overlap specialization

At the exact scale `t * M^(k+1) = N^(k+1)`, Ford's overlap constant reduces
to `2^(k+2) M/k^2 + 1`.  For `k >= 4` this is at most `2^k M`, exactly as
used in the published proof.
-/

namespace GafniTao

noncomputable section

private theorem ford_eight_mul_pow_div_sq_le
    {k : ℕ} (hk : 4 ≤ k) :
    (8 * (2 : ℝ) ^ (k - 1)) / (k : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (k - 1) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hkpos)]
  have hp : 0 ≤ (2 : ℝ) ^ (k - 1) := by positivity
  nlinarith [sq_nonneg ((k : ℝ) - 4)]

theorem ford_two_pow_div_sq_le_half
    {k : ℕ} (hk : 4 ≤ k) :
    (2 : ℝ) ^ (k + 2) / (k : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (k - 1) := by
  rw [show k + 2 = (k - 1) + 3 by omega, pow_add]
  norm_num
  simpa [mul_comm] using ford_eight_mul_pow_div_sq_le hk

theorem fordLemma63W_eq_of_exact_scale
    {N k M : ℕ} {t : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (ht : 0 < t)
    (hscale : t * (M : ℝ) ^ (k + 1) = (N : ℝ) ^ (k + 1)) :
    fordLemma63W N k M t =
      (2 : ℝ) ^ (k + 2) * M / (k : ℝ) ^ 2 + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  unfold fordLemma63W
  field_simp [ne_of_gt hkR, ne_of_gt hMR, ne_of_gt ht]
  rw [← hscale]
  ring

theorem fordLemma63W_le_source_scale
    {N k M : ℕ} {t : ℝ}
    (hk : 4 ≤ k) (hM : 1 ≤ M) (ht : 0 < t)
    (hscale : t * (M : ℝ) ^ (k + 1) = (N : ℝ) ^ (k + 1)) :
    fordLemma63W N k M t ≤ (2 : ℝ) ^ k * M := by
  rw [fordLemma63W_eq_of_exact_scale (by omega) hM ht hscale]
  let P : ℝ := (2 : ℝ) ^ (k - 1)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hcoef :
      (2 : ℝ) ^ (k + 2) / (k : ℝ) ^ 2 ≤ P := by
    simpa [P] using ford_two_pow_div_sq_le_half hk
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hone : (1 : ℝ) ≤ P * M := by
    have hPone : (1 : ℝ) ≤ P := by
      dsimp [P]
      exact one_le_pow₀ (by norm_num)
    nlinarith
  have hfirst :
      (2 : ℝ) ^ (k + 2) * M / (k : ℝ) ^ 2 ≤ P * M := by
    calc
      (2 : ℝ) ^ (k + 2) * M / (k : ℝ) ^ 2 =
          ((2 : ℝ) ^ (k + 2) / (k : ℝ) ^ 2) * M := by ring
      _ ≤ P * M := by gcongr
  have hpow : (2 : ℝ) ^ k = 2 * P := by
    calc
      (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * P := by simp [P, mul_comm]
  rw [hpow]
  nlinarith

#print axioms fordLemma63W_eq_of_exact_scale
#print axioms fordLemma63W_le_source_scale

end

end GafniTao
