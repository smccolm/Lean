import TaoTrudgianYang2025.BetaTaylorPolynomialJets

/-!
# Uniform local finite Taylor remainders

The polynomial uses the ordinary derivatives at an interior anchor.
Taylor's theorem on the genuine segment gives a bound involving only
the original highest derivative on that segment, for either orientation.
-/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem taylorWithinEval_uIcc_eq_finiteTaylorPolynomial
    {f : ℝ → ℝ} {a x : ℝ} (hax : a ≠ x)
    (hf : ContDiffAt ℝ ∞ f a) (n : ℕ) :
    taylorWithinEval f n (uIcc a x) a x = finiteTaylorPolynomial f n a x := by
  have hlt : min a x < max a x := by
    rcases lt_or_gt_of_ne hax with h | h
    · simpa only [min_eq_left h.le,max_eq_right h.le] using h
    · simpa only [min_eq_right h.le,max_eq_left h.le] using h
  have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_Icc hlt
  rw [taylor_within_apply,finiteTaylorPolynomial,taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv hu
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)) left_mem_uIcc,
    iteratedDerivWithin_univ]

theorem abs_finiteTaylorPolynomial_remainder_le
    {f : ℝ → ℝ} {a x M : ℝ} (n : ℕ)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (n+1) f y| ≤ M) :
    |f x-finiteTaylorPolynomial f n a x| ≤
      M*|x-a|^(n+1)/(n+1).factorial := by
  by_cases hax : a = x
  · subst x
    simp only [finiteTaylorPolynomial,taylorWithinEval_self,sub_self,abs_zero,
      zero_pow (Nat.succ_ne_zero n),mul_zero,zero_div,le_refl]
  · have hn : ((n+1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
    obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      (fun z hz => ((hf z hz).of_le hn).contDiffWithinAt)
    rw [taylorWithinEval_uIcc_eq_finiteTaylorPolynomial hax (hf a left_mem_uIcc) n] at he
    rw [he,abs_div,abs_mul,abs_pow,Nat.abs_cast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb y (Ioo_subset_Icc_self hy))
        (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)

theorem iteratedDeriv_real_comp_order (i j : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i+j) f := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]

theorem abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le
    {f : ℝ → ℝ} {a x M : ℝ} {j Q : ℕ} (hj : j ≤ Q)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) :
    |iteratedDeriv j (fun y => f y-finiteTaylorPolynomial f Q a y) x| ≤
      M*|x-a|^(Q+1-j) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb a left_mem_uIcc)
  have hN : (j : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [iteratedDeriv_fun_sub ((hf x right_mem_uIcc).of_le hN)
    ((finiteTaylorPolynomial_contDiff f Q a).contDiffAt.of_le hN),
    iteratedDeriv_finiteTaylorPolynomial f a hj]
  have h := abs_finiteTaylorPolynomial_remainder_le (f := iteratedDeriv j f)
    (a := a) (x := x) (M := M) (Q-j)
    (fun y hy => contDiffAt_iteratedDeriv_infty (hf y hy) j) ?_
  · have hfac : (1 : ℝ) ≤ ((Q-j+1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (Q-j+1))
    exact h.trans ((div_le_self (mul_nonneg hM (pow_nonneg (abs_nonneg _) _)) hfac).trans_eq
      (by rw [show Q-j+1 = Q+1-j by omega]))
  · intro y hy
    rw [iteratedDeriv_real_comp_order,show Q-j+1+j = Q+1 by omega]
    exact hb y hy

end TaoTrudgianYang2025
