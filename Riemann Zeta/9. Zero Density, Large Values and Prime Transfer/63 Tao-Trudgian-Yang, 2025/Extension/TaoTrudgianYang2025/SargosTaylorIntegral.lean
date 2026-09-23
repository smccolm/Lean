import TaoTrudgianYang2025.SargosSymmetricTaylor

/-! Genuine local Taylor integral remainders in ordinary derivatives. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargos_taylor_integral_remainder {f : ℝ → ℝ} {a x : ℝ}
    (hf : ∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y) (n : ℕ) :
    f x-finiteTaylorPolynomial f n a x =
      ∫ t in a..x, ((x-t)^n/(n.factorial:ℝ))*iteratedDeriv (n+1) f t := by
  by_cases hax : a=x
  · subst x
    simp [finiteTaylorPolynomial]
  · have hu : UniqueDiffOn ℝ (uIcc a x) := uniqueDiffOn_Icc (by
      rcases lt_or_gt_of_ne hax with h | h
      · simpa only [min_eq_left h.le,max_eq_right h.le] using h
      · simpa only [min_eq_right h.le,max_eq_left h.le] using h)
    have hn : ((n+1:ℕ) : WithTop ℕ∞) ≤ ∞ :=
      ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
    have h := taylor_integral_remainder (n := n)
      (fun y hy => ((hf y hy).of_le hn).contDiffWithinAt)
    rw [taylorWithinEval_uIcc_eq_finiteTaylorPolynomial hax (hf a left_mem_uIcc) n] at h
    rw [h]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hf t ht).of_le hn) ht,smul_eq_mul]

theorem sargos_taylor_polynomial_shift (f : ℝ → ℝ) (m n : ℝ) :
    finiteTaylorPolynomial (fun x => f (m+x)) 5 0 n =
      finiteTaylorPolynomial f 5 m (m+n) := by
  simp only [finiteTaylorPolynomial,taylor_within_apply,iteratedDerivWithin_univ,
    iteratedDeriv_comp_const_add,add_zero,sub_zero,add_sub_cancel_left]

theorem sargos_taylor_polynomial_reflect (f : ℝ → ℝ) (m n : ℝ) :
    finiteTaylorPolynomial (fun x => f (m-x)) 5 0 n =
      finiteTaylorPolynomial f 5 m (m-n) := by
  simp only [finiteTaylorPolynomial,taylor_within_apply,iteratedDerivWithin_univ,
    iteratedDeriv_comp_const_sub,sub_zero,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have he : m-n-m = -n := by ring
  rw [he,neg_pow]
  ring

end TaoTrudgianYang2025
