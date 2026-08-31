import GafniTao.SharpPerronCutoff

/-!
# Termwise sharp Perron error bounds

These three lemmas cover the strict lower range, the integral endpoint, and
the strict upper range.  They are kept separate so that no endpoint convention
is hidden when the global von Mangoldt sum is estimated.
-/

namespace GafniTao

/-- Termwise error below the cutoff. -/
theorem norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_of_natCast_lt
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : (n : ℝ) < x) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      ArithmeticFunction.vonMangoldt n *
        ((x / (n : ℝ)) ^ c /
          (Real.pi * T * Real.log (x / (n : ℝ)))) := by
  have hcut : sharpPerronCutoff x n = 1 := by
    simp [sharpPerronCutoff, hnx.le]
  rw [hcut]
  have hfactor :
      (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
          (ArithmeticFunction.vonMangoldt n : ℂ) * 1 =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (sharpPerronKernel c T x n - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_mul_of_nonneg_left
    (norm_sharpPerronKernel_sub_one_le_of_natCast_lt hc hT hx hn hnx)
    ArithmeticFunction.vonMangoldt_nonneg

/-- Termwise error above the cutoff. -/
theorem norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_of_lt_natCast
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hxn : x < (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      ArithmeticFunction.vonMangoldt n *
        ((x / (n : ℝ)) ^ c /
          (Real.pi * T * (-Real.log (x / (n : ℝ))))) := by
  have hnle : ¬ (n : ℝ) ≤ x := not_le_of_gt hxn
  have hcut : sharpPerronCutoff x n = 0 := by
    simp [sharpPerronCutoff, hnle]
  rw [hcut, mul_zero, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_mul_of_nonneg_left
    (norm_sharpPerronKernel_le_of_natCast_lt hc hT hx hn hxn)
    ArithmeticFunction.vonMangoldt_nonneg

/-- Termwise error at the integral cutoff.  The displayed `+1` is the exact
cost of comparing the finite kernel with the right-inclusive cutoff value. -/
theorem norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_at_natCast
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x = (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      ArithmeticFunction.vonMangoldt n *
        (|T| / (Real.pi * c) + 1) := by
  have hnle : (n : ℝ) ≤ x := hxn.symm.le
  have hcut : sharpPerronCutoff x n = 1 := by
    simp [sharpPerronCutoff, hnle]
  rw [hcut]
  have hfactor :
      (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
          (ArithmeticFunction.vonMangoldt n : ℂ) * 1 =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (sharpPerronKernel c T x n - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  calc
    ‖sharpPerronKernel c T x n - 1‖ ≤
        ‖sharpPerronKernel c T x n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ |T| / (Real.pi * c) + 1 := by
      simpa using add_le_add_right
        (norm_sharpPerronKernel_at_natCast_le hc hx hn hxn) 1

end GafniTao
