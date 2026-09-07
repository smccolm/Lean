import GafniTao.SharpPerronOptimalLine

/-!
# The positive von Mangoldt Dirichlet series on the optimized line

The far part of the sharp-Perron error is controlled by the genuine
logarithmic derivative of zeta.  This file identifies its norm on a positive
real argument with the nonnegative real von Mangoldt series and then applies
the frozen foundation's vertical-line estimate.
-/

open scoped ComplexOrder

namespace GafniTao

theorem re_LSeriesTerm_vonMangoldt_ofReal
    {c : ℝ} (n : ℕ) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (c : ℂ) n).re =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn]
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    change
      (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) /
          (((n : ℝ) : ℂ) ^ (c : ℂ))).re =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
    rw [← Complex.ofReal_cpow hnpos.le]
    simp

theorem tsum_vonMangoldt_div_rpow_eq_norm_logDerivative
    {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) =
      ‖-deriv riemannZeta (c : ℂ) / riemannZeta (c : ℂ)‖ := by
  have hc' : 1 < ((c : ℂ)).re := by simpa using hc
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hc'
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hc']
  unfold LSeries
  rw [← Complex.re_eq_norm.mpr, Complex.re_tsum hsum]
  · congr 1
    funext n
    exact (re_LSeriesTerm_vonMangoldt_ofReal n).symm
  · apply tsum_nonneg
    intro n
    exact LSeries.term_nonneg
      (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg) c

theorem summable_vonMangoldt_div_nat_rpow
    {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
  have hc' : 1 < ((c : ℂ)).re := by simpa using hc
  have hcomplex := ArithmeticFunction.LSeriesSummable_vonMangoldt hc'
  have hreal := summable_complex_then_summable_real_part _ hcomplex
  refine hreal.congr (fun n => ?_)
  exact re_LSeriesTerm_vonMangoldt_ofReal n

/-- A uniform `log y + C` bound for the positive von Mangoldt series at the
optimized Perron abscissa. -/
theorem exists_tsum_vonMangoldt_optimized_le :
    ∃ C ≥ 0, ∀ y : ℝ, 1 < y →
      (∑' n : ℕ,
        ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ sharpPerronAbscissa y) ≤ Real.log y + C := by
  obtain ⟨C, hC, hbound⟩ := triv_bound_zeta
  refine ⟨C, hC, fun y hy => ?_⟩
  have hc := one_lt_sharpPerronAbscissa hy
  rw [tsum_vonMangoldt_div_rpow_eq_norm_logDerivative hc]
  have hz := hbound (sharpPerronAbscissa y) 0 hc
  simpa [sharpPerronAbscissa_sub_one hy] using hz

end GafniTao
