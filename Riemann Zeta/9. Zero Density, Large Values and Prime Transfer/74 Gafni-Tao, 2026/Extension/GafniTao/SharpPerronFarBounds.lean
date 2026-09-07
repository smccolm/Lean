import GafniTao.SharpPerronNearBounds

/-!
# Nonresonant Perron summands

Outside `y/2 < n < 2y`, the additive-distance factor is at most two.  The
remaining summand is a fixed multiple of the absolutely convergent von
Mangoldt Dirichlet series.
-/

namespace GafniTao

theorem max_div_abs_sub_le_two_of_far
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hfar : z ≤ y / 2 ∨ 2 * y ≤ z) :
    max y z / |y - z| ≤ 2 := by
  rcases hfar with hlow | hhigh
  · have hzy : z ≤ y := by linarith
    rw [max_eq_left hzy, abs_of_nonneg (sub_nonneg.mpr hzy)]
    have hden : 0 < y - z := by linarith
    rw [div_le_iff₀ hden]
    linarith
  · have hyz : y ≤ z := by linarith
    rw [max_eq_right hyz, abs_of_nonpos (sub_nonpos.mpr hyz), neg_sub]
    have hden : 0 < z - y := by linarith
    rw [div_le_iff₀ hden]
    linarith

/-- Pointwise nonresonant estimate by the positive Dirichlet-series term. -/
theorem norm_vonMangoldt_halfPoint_cutoffError_le_far
    {T x : ℝ} {n : ℕ}
    (hy : 2 ≤ sharpPerronHalfPoint x) (hT : 0 < T)
    (hn : 1 ≤ n)
    (hfar : (n : ℝ) ≤ sharpPerronHalfPoint x / 2 ∨
      2 * sharpPerronHalfPoint x ≤ (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel (sharpPerronAbscissa (sharpPerronHalfPoint x)) T
            (sharpPerronHalfPoint x) n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff (sharpPerronHalfPoint x) n‖ ≤
      (2 * (sharpPerronHalfPoint x ^
          sharpPerronAbscissa (sharpPerronHalfPoint x)) /
          (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ sharpPerronAbscissa (sharpPerronHalfPoint x))) := by
  let y := sharpPerronHalfPoint x
  let c := sharpPerronAbscissa y
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hc0 : 0 < c := by
    exact sharpPerronAbscissa_pos (by dsimp [y]; linarith)
  have hfactor := max_div_abs_sub_le_two_of_far hy0 hn0 hfar
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hLambda0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hpow0 : 0 ≤ (y / (n : ℝ)) ^ c :=
    Real.rpow_nonneg (div_pos hy0 hn0).le _
  refine (norm_vonMangoldt_halfPoint_cutoffError_le_additive
    hc0 hT hn).trans ?_
  change
    (ArithmeticFunction.vonMangoldt n * (y / (n : ℝ)) ^ c /
        (Real.pi * T)) * (max y (n : ℝ) / |y - (n : ℝ)|) ≤
      (2 * y ^ c / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c)
  calc
    (ArithmeticFunction.vonMangoldt n * (y / (n : ℝ)) ^ c /
          (Real.pi * T)) *
        (max y (n : ℝ) / |y - (n : ℝ)|) ≤
      (ArithmeticFunction.vonMangoldt n * (y / (n : ℝ)) ^ c /
          (Real.pi * T)) * 2 := by
            exact mul_le_mul_of_nonneg_left hfactor
              (div_nonneg (mul_nonneg hLambda0 hpow0) hpiT.le)
    _ = (2 * y ^ c / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
          rw [Real.div_rpow hy0.le hn0.le]
          ring

end GafniTao
