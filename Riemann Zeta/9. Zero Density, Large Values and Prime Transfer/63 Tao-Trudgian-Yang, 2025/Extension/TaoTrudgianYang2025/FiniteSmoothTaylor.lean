import TaoTrudgianYang2025.BetaTaylorPolynomialRemainder

/-! Local Taylor estimates with exactly finite smoothness.
These do not require infinite differentiability of the source phase. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem contDiffAt_iteratedDeriv_finite {f : ℝ → ℝ} {x : ℝ} {n j : ℕ}
    (hf : ContDiffAt ℝ (n+j) f x) :
    ContDiffAt ℝ n (iteratedDeriv j f) x := by
  induction j generalizing n with
  | zero => simpa only [Nat.add_zero,iteratedDeriv_zero] using hf
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hh : ContDiffAt ℝ ((n+1)+j) f x := by
        simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ,add_assoc,add_comm,add_left_comm]
          using hf
      exact (ih hh).derivWithin (by simp)

theorem taylorWithinEval_uIcc_eq_finiteTaylorPolynomial_finite
    {f : ℝ → ℝ} {a x : ℝ} {n : ℕ} (hax : a ≠ x)
    (hf : ContDiffAt ℝ n f a) :
    taylorWithinEval f n (uIcc a x) a x = finiteTaylorPolynomial f n a x := by
  have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne hax with h | h
    · simpa only [min_eq_left h.le,max_eq_right h.le] using h
    · simpa only [min_eq_right h.le,max_eq_left h.le] using h)
  rw [taylor_within_apply,finiteTaylorPolynomial,taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have ht := Finset.mem_range.mp hj; omega
  have hjn' : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hjn
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le hjn') left_mem_uIcc,
    iteratedDerivWithin_univ]

theorem abs_finiteTaylorPolynomial_remainder_le_finite
    {f : ℝ → ℝ} {a x M : ℝ} (n : ℕ)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ (n+1) f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (n+1) f y| ≤ M) :
    |f x-finiteTaylorPolynomial f n a x| ≤
      M*|x-a|^(n+1)/(n+1).factorial := by
  by_cases hax : a = x
  · subst x
    simp only [finiteTaylorPolynomial,taylorWithinEval_self,sub_self,abs_zero,
      zero_pow (Nat.succ_ne_zero n),mul_zero,zero_div,le_refl]
  · obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      (fun z hz => (hf z hz).contDiffWithinAt)
    rw [taylorWithinEval_uIcc_eq_finiteTaylorPolynomial_finite hax
      ((hf a left_mem_uIcc).of_le (by simp))] at he
    rw [he,abs_div,abs_mul,abs_pow,Nat.abs_cast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb y (Ioo_subset_Icc_self hy))
        (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)

theorem abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le_finite
    {f : ℝ → ℝ} {a x M : ℝ} {j Q : ℕ} (hj : j ≤ Q)
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ (Q+1) f y)
    (hb : ∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) :
    |iteratedDeriv j (fun y => f y-finiteTaylorPolynomial f Q a y) x| ≤
      M*|x-a|^(Q+1-j) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb a left_mem_uIcc)
  have hjQ : (j : WithTop ℕ∞) ≤ Q+1 := by exact_mod_cast (by omega : j ≤ Q+1)
  have hjtop : (j : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  rw [iteratedDeriv_fun_sub ((hf x right_mem_uIcc).of_le hjQ)
    ((finiteTaylorPolynomial_contDiff f Q a).contDiffAt.of_le hjtop),
    iteratedDeriv_finiteTaylorPolynomial f a hj]
  have hf' (y : ℝ) (hy : y ∈ uIcc a x) :
      ContDiffAt ℝ (((Q-j+1)+j : ℕ) : WithTop ℕ∞) f y := by
    rw [show Q-j+1+j = Q+1 by omega]
    simpa only [Nat.cast_add,Nat.cast_one] using hf y hy
  have h := abs_finiteTaylorPolynomial_remainder_le_finite
    (f := iteratedDeriv j f) (a := a) (x := x) (M := M) (Q-j)
    (fun y hy => by
      have ht := contDiffAt_iteratedDeriv_finite (n := Q-j+1) (j := j)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hf' y hy)
      simpa only [Nat.cast_add,Nat.cast_one] using ht) ?_
  · have hfac : (1 : ℝ) ≤ ((Q-j+1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (Q-j+1))
    exact h.trans ((div_le_self (mul_nonneg hM (pow_nonneg (abs_nonneg _) _)) hfac).trans_eq
      (by rw [show Q-j+1 = Q+1-j by omega]))
  · intro y hy
    rw [iteratedDeriv_real_comp_order,show Q-j+1+j = Q+1 by omega]
    exact hb y hy

end TaoTrudgianYang2025
