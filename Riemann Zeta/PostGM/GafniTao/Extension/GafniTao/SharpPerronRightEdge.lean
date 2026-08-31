import GafniTao.SharpPerronRectangleSum

/-!
# Identification of the right zeta edge

The right edge of the residue rectangle is exactly the optimized Perron
integral already estimated arithmetically, with no normalization or sign
change hidden in notation.
-/

open Complex Set MeasureTheory
open RiemannZeta.GuthMaynard
open scoped Interval

noncomputable section

namespace GafniTao

/-- The literal optimized logarithmic-derivative Perron integral. -/
noncomputable def sharpZetaPerronRightIntegral (y R : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-R)..R,
      (-deriv riemannZeta
          ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) /
        riemannZeta
          ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I)) *
        (y : ℂ) ^ ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) /
        ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I)

theorem sharpZetaPerronIntegrand_right_line
    {y t : ℝ} (hy : 1 < y) :
    sharpZetaPerronIntegrand y
        ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) =
      (-deriv riemannZeta
          ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) /
        riemannZeta
          ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I)) *
        (y : ℂ) ^ ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) /
        ((sharpPerronAbscissa y : ℂ) + (t : ℂ) * I) := by
  let s : ℂ := (sharpPerronAbscissa y : ℂ) + (t : ℂ) * I
  have hc : 1 < sharpPerronAbscissa y := one_lt_sharpPerronAbscissa hy
  have hsre : s.re = sharpPerronAbscissa y := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hsre] at this
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hsre] at this
    linarith
  have hzeta : riemannZeta s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simpa [hsre]
  rw [show (sharpPerronAbscissa y : ℂ) + (t : ℂ) * I = s from rfl]
  rw [sharpZetaPerronIntegrand_eq hs0 hs1 hzeta, logDeriv_apply]
  ring

/-- The normalized vertical-edge convention agrees exactly with the real
interval Perron convention. -/
theorem VIntegral'_sharpZetaPerronIntegrand_right_eq
    {y R : ℝ} (hy : 1 < y) :
    VIntegral' (sharpZetaPerronIntegrand y)
        (sharpPerronAbscissa y) (-R) R =
      sharpZetaPerronRightIntegral y R := by
  rw [VIntegral', VIntegral, sharpZetaPerronRightIntegral]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_congr
    (fun t _ht => sharpZetaPerronIntegrand_right_line hy)]
  have hscalar :
      (1 / (2 * (Real.pi : ℂ) * I)) * I =
        (1 / (2 * Real.pi) : ℂ) := by
    field_simp [I_ne_zero, Real.pi_ne_zero]
  rw [← mul_assoc, hscalar]

end GafniTao
