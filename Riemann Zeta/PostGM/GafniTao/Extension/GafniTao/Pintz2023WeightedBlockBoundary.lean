import GafniTao.Pintz2023WeightedBlockComplex

/-!
# Endpoint control for Pintz's weighted blocks

Natural floors and ceilings leave at most one term on either side of the
Corollary-3 block.  These lemmas keep those terms explicit and bound them at
the same negative power as the main block.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem pintz2023ComplexWeightedBlock_add
    (xi t : ℝ) {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    pintz2023ComplexWeightedBlock xi A B t +
        pintz2023ComplexWeightedBlock xi B C t =
      pintz2023ComplexWeightedBlock xi A C t := by
  unfold pintz2023ComplexWeightedBlock
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.Ioc_union_Ioc_eq_Ioc hAB hBC]

theorem norm_pintz2023_complex_weighted_term
    {n : ℕ} (hn : 0 < n) (xi t : ℝ) :
    ‖(n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)))‖ =
      (n : ℝ) ^ (xi - 1) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos hnReal]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, ofReal_im,
    I_im, zero_mul, mul_zero, sub_zero]
  congr 1
  ring

/-- A half-open interval containing at most one integer and lying above `Q`
has the exact negative-power bound needed for the rounded endpoints. -/
theorem norm_pintz2023ComplexWeightedBlock_boundary
    {xi epsilon Q t : ℝ} {L U : ℕ}
    (hepsilon : 0 < epsilon) (hxi : xi + 3 * epsilon ≤ 1)
    (hQ : 1 ≤ Q) (hQU : ∀ n ∈ Finset.Ioc L U, Q ≤ (n : ℝ))
    (hUL : U ≤ L + 1) :
    ‖pintz2023ComplexWeightedBlock xi L U t‖ ≤
      Q ^ (-3 * epsilon) := by
  have hcard : (Finset.Ioc L U).card ≤ 1 := by
    rw [Nat.card_Ioc]
    omega
  have hQPos : 0 < Q := zero_lt_one.trans_le hQ
  have hexp : -3 * epsilon ≤ 0 := by linarith
  unfold pintz2023ComplexWeightedBlock
  calc
    ‖∑ n ∈ Finset.Ioc L U,
        (n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)))‖ ≤
        ∑ n ∈ Finset.Ioc L U,
          ‖(n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc L U, (n : ℝ) ^ (xi - 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_pintz2023_complex_weighted_term
        (Nat.pos_of_ne_zero (by
          intro hnZero
          subst n
          exact (Nat.not_lt_zero _ (Finset.mem_Ioc.mp hn).1)))]
    _ ≤ ∑ _n ∈ Finset.Ioc L U, Q ^ (-3 * epsilon) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnNat : 0 < n := by
        have := (Finset.mem_Ioc.mp hn).1
        omega
      have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNat
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast hnNat
      have hAtN : (n : ℝ) ^ (xi - 1) ≤ (n : ℝ) ^ (-3 * epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
      exact hAtN.trans
        (Real.rpow_le_rpow_of_nonpos hQPos (hQU n hn) hexp)
    _ = ((Finset.Ioc L U).card : ℝ) * Q ^ (-3 * epsilon) := by
      simp
    _ ≤ 1 * Q ^ (-3 * epsilon) := by
      gcongr
      exact_mod_cast hcard
    _ = Q ^ (-3 * epsilon) := one_mul _

#print axioms pintz2023ComplexWeightedBlock_add
#print axioms norm_pintz2023_complex_weighted_term
#print axioms norm_pintz2023ComplexWeightedBlock_boundary

end

end GafniTao
