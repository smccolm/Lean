import GafniTao.SharpPerronRectangle

/-!
# Evaluation and edge decomposition of the sharp-Perron residue sum
-/

open Complex Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

namespace GafniTao

theorem zero_not_mem_zeroSet (R : ℝ) : (0 : ℂ) ∉ zeroSet 0 R := by
  intro h
  have hd := mem_zeroSet_zero_data h
  norm_num [riemannZeta_zero] at hd

theorem one_not_mem_zeroSet (R : ℝ) : (1 : ℂ) ∉ zeroSet 0 R := by
  intro h
  have hd := mem_zeroSet_zero_data h
  exact riemannZeta_one_ne_zero hd.2.2.2.2

/-- The finite coefficient sum is the pole term, the literal origin
constant, and the multiplicity-weighted zero sum with the classical minus
sign. -/
theorem sum_sharpZetaPerronResidueCoefficient
    (y R : ℝ) :
    (∑ p ∈ sharpPerronSingularities R,
        sharpZetaPerronResidueCoefficient y p) =
      (-logDeriv sharpZetaSurrogate 0 - 1) + (y : ℂ) -
        ∑ rho ∈ zeroSet 0 R,
          (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho) := by
  classical
  rw [sharpPerronSingularities, Finset.sum_insert]
  · rw [Finset.sum_insert]
    · simp only [sharpZetaPerronResidueCoefficient, if_pos, if_neg one_ne_zero]
      have hsum :
          (∑ rho ∈ zeroSet 0 R,
              sharpZetaPerronResidueCoefficient y rho) =
            -(∑ rho ∈ zeroSet 0 R,
              (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro rho hrho
        have hrho0 : rho ≠ 0 := fun h => zero_not_mem_zeroSet R (h ▸ hrho)
        have hrho1 : rho ≠ 1 := fun h => one_not_mem_zeroSet R (h ▸ hrho)
        simp only [sharpZetaPerronResidueCoefficient, if_neg hrho0,
          if_neg hrho1, sharpPerronMonomial]
        ring
      change (-logDeriv sharpZetaSurrogate 0 - 1) +
          ((y : ℂ) + ∑ rho ∈ zeroSet 0 R,
            sharpZetaPerronResidueCoefficient y rho) = _
      rw [hsum]
      ring
    · exact one_not_mem_zeroSet R
  · simp [zero_not_mem_zeroSet R]

/-- The global rectangle identity in its classical explicit-formula shape. -/
theorem sharpZetaPerron_rectangleIntegral_eq_explicit_sum
    {y R : ℝ} (hy : 1 < y) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    RectangleIntegral' (sharpZetaPerronIntegrand y)
        ((-1 : ℂ) - (R : ℂ) * I)
        ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I) =
      (-logDeriv sharpZetaSurrogate 0 - 1) + (y : ℂ) -
        ∑ rho ∈ zeroSet 0 R,
          (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho) := by
  rw [sharpZetaPerron_rectangleIntegral_eq_residue_sum hy hR hheight,
    sum_sharpZetaPerronResidueCoefficient]

/-- Solving the rectangle identity for its right vertical edge leaves the
three other oriented edges explicitly visible. -/
theorem sharpZetaPerron_rightVertical_eq_explicit_sum_add_edges
    {y R : ℝ} (hy : 1 < y) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    VIntegral' (sharpZetaPerronIntegrand y)
        (sharpPerronAbscissa y) (-R) R =
      ((-logDeriv sharpZetaSurrogate 0 - 1) + (y : ℂ) -
        ∑ rho ∈ zeroSet 0 R,
          (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)) -
      HIntegral' (sharpZetaPerronIntegrand y) (-1)
        (sharpPerronAbscissa y) (-R) +
      HIntegral' (sharpZetaPerronIntegrand y) (-1)
        (sharpPerronAbscissa y) R +
      VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R := by
  have hrect := sharpZetaPerron_rectangleIntegral_eq_explicit_sum
    hy hR hheight
  have hreLeft : ((-1 : ℂ) - (R : ℂ) * I).re = -1 := by simp
  have hreRight :
      ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I).re =
        sharpPerronAbscissa y := by simp
  have himLeft : ((-1 : ℂ) - (R : ℂ) * I).im = -R := by simp
  have himRight :
      ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I).im = R := by simp
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

end GafniTao
