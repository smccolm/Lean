import GafniTao.Pintz2023MellinContour

/-!
# Pintz (2023), Lemma 3.4: oriented Mellin edges

This file relates the removable-singularity contour to the literal right-line
integrand from equation (3.5), and expands the finite rectangle with all four
orientations visible.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators Topology Interval

namespace GafniTao

noncomputable section

theorem pintz2023_RectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pintz2023MellinContourIntegrand_right
    {N : ℕ} (s : ℂ) (t : ℝ) :
    pintz2023MellinContourIntegrand N s
        (((2 : ℝ) : ℂ) + (t : ℂ) * I) =
      pintz2023MellinZetaIntegrand N s t := by
  have hw : (((2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [pintz2023MellinContourIntegrand_eq_source hw]
  rfl

/-- Equation (3.5), now expressed as the right side of the same holomorphic
contour used by the finite residue theorem. -/
theorem pintz2023SmoothedZetaSum_eq_right_contour
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 0 ≤ s.re) :
    pintz2023SmoothedZetaSum N s =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ t : ℝ, pintz2023MellinContourIntegrand N s
          (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  rw [pintz2023SmoothedZetaSum_eq_right_mellin hN hs]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact (pintz2023MellinContourIntegrand_right s t).symm

#print axioms pintz2023_RectangleIntegral'_eq_edges
#print axioms pintz2023SmoothedZetaSum_eq_right_contour

end


end GafniTao
