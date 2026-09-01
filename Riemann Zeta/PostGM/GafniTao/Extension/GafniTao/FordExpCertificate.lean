import GafniTao.FordNormalizedIntegralCenter

/-!
# Kernel-checkable exponential enclosures for Ford's numerical integral

Ford's numerical constant is too tight for a coarse analytic estimate.  We
therefore expose a finite Taylor upper enclosure and an exact argument-scaling
lemma.  Numerical certificates built from these declarations reduce to finite
rational arithmetic in the kernel.
-/

open Finset

namespace GafniTao

noncomputable section

def fordExpTaylorUpper (n : ℕ) (x : ℝ) : ℝ :=
  (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
    |x| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n))

theorem real_exp_le_fordExpTaylorUpper
    {n : ℕ} {x : ℝ} (hn : 0 < n) (hx : |x| ≤ 1) :
    Real.exp x ≤ fordExpTaylorUpper n x := by
  have h := Real.exp_bound hx hn
  have hleft :
      Real.exp x - (∑ m ∈ Finset.range n, x ^ m / m.factorial) ≤
        |Real.exp x -
          (∑ m ∈ Finset.range n, x ^ m / m.factorial)| :=
    le_abs_self _
  unfold fordExpTaylorUpper
  linarith

theorem fordExpTaylorUpper_pos
    {n : ℕ} {x : ℝ} (hn : 0 < n) (hx : |x| ≤ 1) :
    0 < fordExpTaylorUpper n x :=
  (Real.exp_pos x).trans_le (real_exp_le_fordExpTaylorUpper hn hx)

/-- Reduce an arbitrary nonnegative exponential argument by a positive natural
scaling factor before applying the finite Taylor enclosure. -/
theorem real_exp_neg_le_scaledTaylor
    {z : ℝ} {m n : ℕ}
    (hz : 0 ≤ z) (hm : 0 < m) (hn : 0 < n)
    (hscale : z ≤ m) :
    Real.exp (-z) ≤
      fordExpTaylorUpper n (-z / m) ^ m := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hxAbs : |-z / (m : ℝ)| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_nonneg hz, abs_of_pos hmReal]
    exact (div_le_one hmReal).2 hscale
  have hbase := real_exp_le_fordExpTaylorUpper hn hxAbs
  have hpow := pow_le_pow_left₀ (Real.exp_pos (-z / (m : ℝ))).le hbase m
  calc
    Real.exp (-z) = Real.exp ((m : ℝ) * (-z / (m : ℝ))) := by
      congr 1
      field_simp [hmReal.ne']
    _ = Real.exp (-z / (m : ℝ)) ^ m :=
      Real.exp_nat_mul (-z / (m : ℝ)) m
    _ ≤ fordExpTaylorUpper n (-z / (m : ℝ)) ^ m := hpow

#print axioms real_exp_le_fordExpTaylorUpper
#print axioms real_exp_neg_le_scaledTaylor

end

end GafniTao
