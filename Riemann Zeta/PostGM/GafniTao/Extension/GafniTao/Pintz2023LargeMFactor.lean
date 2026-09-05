import GafniTao.Pintz2023LargeMReindex

/-!
# Pintz (2023), equation (4.14): factorized large-`m` block

The exact rectangular divisor-pair sum is factored into the Möbius term in
`d` and the weighted Dirichlet block in `m`.  This is the algebraic entry
bridge required before Corollary 3 can be applied to each dyadic `m` block.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

noncomputable section

/-- The complementary-factor sum for one fixed Möbius divisor. -/
noncomputable def pintz2023LargeMInnerBlock
    (Y d : ℕ) (Iset : Finset ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (Y + 1),
    if d * m ∈ Iset ∧ R < (m : ℝ) then
      (m : ℂ) ^ (-s)
    else 0

/-- The source-factorized form of the large-`m` contribution. -/
noncomputable def pintz2023LargeMFactorizedBlock
    (X Y : ℕ) (Iset : Finset ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (Y + 1),
    if d ≤ X then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (d : ℂ) ^ (-s) * pintz2023LargeMInnerBlock Y d Iset R s
    else 0

/-- Exact factorization of the divisor-pair rectangle in equation (4.14). -/
theorem pintz2023LargeMRectangleBlock_eq_factorized
    (X Y : ℕ) (Iset : Finset ℕ) (R : ℝ) (s : ℂ) :
    pintz2023LargeMRectangleBlock X Y Iset R s =
      pintz2023LargeMFactorizedBlock X Y Iset R s := by
  classical
  unfold pintz2023LargeMRectangleBlock pintz2023LargeMFactorizedBlock
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdX : d ≤ X
  · rw [if_pos hdX]
    unfold pintz2023LargeMInnerBlock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hterm : d * m ∈ Iset ∧ R < (m : ℝ)
    · rw [if_pos ⟨hdX, hterm⟩, if_pos hterm]
      have hdNonneg : (0 : ℝ) ≤ d := by positivity
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      have hpow := Complex.mul_cpow_ofReal_nonneg hdNonneg hmNonneg (-s)
      push_cast at hpow
      rw [hpow]
      ring
    · rw [if_neg]
      · rw [if_neg hterm, mul_zero]
      · intro h
        exact hterm h.2
  · rw [if_neg hdX]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    exact hdX h.1

/-- Complete exact entry bridge from the large coefficient portion of an
arbitrary source interval to its factorized `d,m` sum. -/
theorem pintz2023SplitLargeM_eq_factorized
    {X Y : ℕ} {Iset : Finset ℕ} {R : ℝ} {s : ℂ}
    (hIset : Iset ⊆ Finset.Ioc 0 Y) :
    pintz2023SplitIntervalBlock
        (fun n => pintz2023LargeMCoeff X n R) Iset s =
      pintz2023LargeMFactorizedBlock X Y Iset R s := by
  rw [pintz2023SplitLargeM_eq_rectangle hIset,
    pintz2023LargeMRectangleBlock_eq_factorized]

#print axioms pintz2023LargeMRectangleBlock_eq_factorized
#print axioms pintz2023SplitLargeM_eq_factorized

end

end GafniTao
