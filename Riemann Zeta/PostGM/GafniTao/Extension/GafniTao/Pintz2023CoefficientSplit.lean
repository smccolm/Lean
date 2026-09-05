import GafniTao.Pintz2023HighZeroSelection
import GafniTao.Pintz2023CorollaryThree

/-!
# Pintz (2023), equation (4.13)

The coefficient of `zeta(s) M_X(s)` is split according to whether the
complementary divisor `m = n / d` lies above or below the literal critical
scale.  Both pieces remain finite divisor sums, and their recombination is
an exact equality.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

noncomputable section

/-- The `a'_n` portion of Pintz (4.13), with `m > R`. -/
noncomputable def pintz2023LargeMCoeff
    (X n : ℕ) (R : ℝ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ X),
    if R < (n / d : ℕ) then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)
    else 0

/-- The `a''_n` portion of Pintz (4.13), with `m <= R`. -/
noncomputable def pintz2023SmallMCoeff
    (X n : ℕ) (R : ℝ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ X),
    if (n / d : ℕ) ≤ R then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)
    else 0

/-- Exact coefficient identity `a_n = a'_n + a''_n` in (4.13). -/
theorem pintz2023Coeff_eq_largeM_add_smallM
    (X n : ℕ) (R : ℝ) :
    pintz2023Coeff X n =
      pintz2023LargeMCoeff X n R + pintz2023SmallMCoeff X n R := by
  classical
  rw [pintz2023Coeff_eq_divisor_sum]
  unfold pintz2023LargeMCoeff pintz2023SmallMCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hlarge : R < (n / d : ℕ)
  · rw [if_pos hlarge, if_neg (not_le.mpr hlarge), add_zero]
  · rw [if_neg hlarge, if_pos (le_of_not_gt hlarge), zero_add]

/-- A source interval carrying one of the two coefficient pieces. -/
noncomputable def pintz2023SplitIntervalBlock
    (coeff : ℕ → ℂ) (Iset : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Iset, coeff n * (n : ℂ) ^ (-s)

/-- Equation (4.13) summed over an arbitrary finite source interval. -/
theorem pintz2023IntervalBlock_eq_largeM_add_smallM
    (X : ℕ) (Iset : Finset ℕ) (R : ℝ) (s : ℂ) :
    pintz2023IntervalBlock X Iset s =
      pintz2023SplitIntervalBlock
          (fun n => pintz2023LargeMCoeff X n R) Iset s +
        pintz2023SplitIntervalBlock
          (fun n => pintz2023SmallMCoeff X n R) Iset s := by
  classical
  unfold pintz2023IntervalBlock pintz2023SplitIntervalBlock
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← add_mul, ← pintz2023Coeff_eq_largeM_add_smallM]

/-- Divisor-pair form of the large-`m` coefficient.  This is the exact
finite reindexing used before applying Pintz Corollary 3 in (4.14). -/
theorem pintz2023LargeMCoeff_eq_antidiagonal
    (n X : ℕ) (R : ℝ) :
    pintz2023LargeMCoeff X n R =
      ∑ p ∈ n.divisorsAntidiagonal,
        if p.1 ≤ X ∧ R < (p.2 : ℝ) then
          ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)
        else 0 := by
  classical
  unfold pintz2023LargeMCoeff
  rw [← Nat.map_div_right_divisors]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdLe : d ≤ X
  · simp only [hdLe, true_and, if_true]
  · simp only [hdLe, false_and, if_false]

#print axioms pintz2023Coeff_eq_largeM_add_smallM
#print axioms pintz2023IntervalBlock_eq_largeM_add_smallM
#print axioms pintz2023LargeMCoeff_eq_antidiagonal

end

end GafniTao
