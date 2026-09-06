import GafniTao.Pintz2023SmallMSurvival

/-!
# Pintz (2023), equation (4.15): literal support of the surviving block

The two scales in Pintz's Section 4 are different.  The coefficient split is
made at `N_k(T)`, while the surviving small-`m` block is supported only below
`X * N_k(T) = N_k^*(T)`.  This module proves that implication directly from
the finite divisor sum used in equation (4.13).
-/

open Complex Finset

namespace GafniTao

noncomputable section

/-- A positive surviving small-`m` block forces its dyadic left endpoint to
lie strictly below the literal product support `X * R`. -/
theorem pintz2023LocalizedSmallMBlock_left_lt_scale
    {X Y r : ℕ} {R V : ℝ} {s : ℂ}
    (hR : 0 ≤ R) (hV : 0 < V)
    (hBlock : V ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R)
        (pintz2023LocalizedInterval X Y r) s‖) :
    ((2 ^ r * X : ℕ) : ℝ) < (X : ℝ) * R := by
  by_contra hnot
  have hleft : (X : ℝ) * R ≤ ((2 ^ r * X : ℕ) : ℝ) := le_of_not_gt hnot
  have hzero :
      pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R)
        (pintz2023LocalizedInterval X Y r) s = 0 := by
    unfold pintz2023SplitIntervalBlock
    apply Finset.sum_eq_zero
    intro n hn
    have hnDyadic := pintz2023LocalizedInterval_subset_dyadic X Y r hn
    have hnLowerNat : 2 ^ r * X < n := (Finset.mem_Ioc.mp hnDyadic).1
    have hnLower : ((2 ^ r * X : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hnLowerNat
    have hscale : (X : ℝ) * R < (n : ℝ) := hleft.trans_lt hnLower
    change pintz2023SmallMCoeff X n R * (n : ℂ) ^ (-s) = 0
    rw [pintz2023SmallMCoeff_eq_zero_of_scale_lt hR hscale, zero_mul]
  rw [hzero, norm_zero] at hBlock
  linarith

#print axioms pintz2023LocalizedSmallMBlock_left_lt_scale

end

end GafniTao
