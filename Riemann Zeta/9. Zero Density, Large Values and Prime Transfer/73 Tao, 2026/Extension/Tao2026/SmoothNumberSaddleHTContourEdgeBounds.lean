import Tao2026.SmoothNumberSaddleHTPerronAbsorption

/-!
# Sup-norm reduction for the three HT contour edges

This module removes the contour-integration geometry from the remaining
Hildebrand--Tenenbaum edge estimate.  A uniform pointwise bound on each
horizontal edge and on the left vertical edge is converted into an exact
bound for `smoothSaddleHTContourEdgeContribution`, including the `1/(2πi)`
normalization and the literal source edge lengths.

The remaining analytic task is consequently pointwise: bound the translated
zeta logarithmic derivative on the three zero-free boundary segments.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

private theorem norm_perronContourScalar :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I) : ℂ)‖ =
      1 / (2 * Real.pi) := by
  simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I]
  ring

/-- A pointwise bound on a horizontal segment controls its normalized
contour integral by the bound times the segment length. -/
theorem norm_HIntegral'_le_of_norm_le_const
    {f : ℂ → ℂ} {left right height M : ℝ}
    (hlr : left ≤ right)
    (hpoint : ∀ x ∈ Set.Icc left right,
      ‖f ((x : ℂ) + (height : ℂ) * Complex.I)‖ ≤ M) :
    ‖HIntegral' f left right height‖ ≤
      (1 / (2 * Real.pi)) * M * (right - left) := by
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => f ((x : ℂ) + (height : ℂ) * Complex.I))
    (a := left) (b := right) (C := M)
    (fun x hx => hpoint x (by
      have hu := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hlr] using hu))
  have habs : |right - left| = right - left :=
    abs_of_nonneg (sub_nonneg.mpr hlr)
  rw [HIntegral', HIntegral]
  simp only [smul_eq_mul, norm_mul, norm_perronContourScalar]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ x in left..right,
          f ((x : ℂ) + (height : ℂ) * Complex.I)‖ ≤
      (1 / (2 * Real.pi)) * (M * |right - left|) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (1 / (2 * Real.pi)) * M * (right - left) := by
      rw [habs]
      ring

/-- A pointwise bound on a vertical segment controls its normalized contour
integral by the bound times the segment length. -/
theorem norm_VIntegral'_le_of_norm_le_const
    {f : ℂ → ℂ} {line bottom top M : ℝ}
    (hbt : bottom ≤ top)
    (hpoint : ∀ u ∈ Set.Icc bottom top,
      ‖f ((line : ℂ) + (u : ℂ) * Complex.I)‖ ≤ M) :
    ‖VIntegral' f line bottom top‖ ≤
      (1 / (2 * Real.pi)) * M * (top - bottom) := by
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ => f ((line : ℂ) + (u : ℂ) * Complex.I))
    (a := bottom) (b := top) (C := M)
    (fun u hu => hpoint u (by
      have hu' := Set.uIoc_subset_uIcc hu
      simpa [Set.uIcc_of_le hbt] using hu'))
  have habs : |top - bottom| = top - bottom :=
    abs_of_nonneg (sub_nonneg.mpr hbt)
  rw [VIntegral', VIntegral]
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, one_mul,
    norm_perronContourScalar]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ u in bottom..top,
          f ((line : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      (1 / (2 * Real.pi)) * (M * |top - bottom|) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (1 / (2 * Real.pi)) * M * (top - bottom) := by
      rw [habs]
      ring

/-- The exact scalar majorant obtained from common horizontal and vertical
pointwise bounds on the source HT rectangle. -/
noncomputable def smoothSaddleHTContourEdgeSupMajorant
    (y : ℕ) (ε horizontalBound verticalBound : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (2 * horizontalBound *
        (smoothSaddleHTContourShift y ε + 1 / Real.log y) +
      2 * verticalBound * smoothSaddleHTContourHeight y ε)

theorem smoothSaddleHTContour_horizontal_length
    (y : ℕ) (beta ε : ℝ) :
    smoothSaddleHTContourRight y beta -
        (beta - smoothSaddleHTContourShift y ε) =
      smoothSaddleHTContourShift y ε + 1 / Real.log y := by
  unfold smoothSaddleHTContourRight
  ring

/-- The three pointwise boundary estimates imply the complete edge bound.
No measurability or integrability hypotheses are needed separately: the
interval-integral norm inequality is valid with the totalized integral. -/
theorem norm_smoothSaddleHTContourEdgeContribution_le_supMajorant
    {y : ℕ} {beta ε t horizontalBound verticalBound : ℝ}
    (hy : 2 ≤ y)
    (hbottom : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) -
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (htop : ∀ x ∈ Set.Icc
        (beta - smoothSaddleHTContourShift y ε)
        (smoothSaddleHTContourRight y beta),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          ((x : ℂ) +
            (smoothSaddleHTContourHeight y ε : ℂ) * Complex.I)‖ ≤
        horizontalBound)
    (hleft : ∀ u ∈ Set.Icc
        (-smoothSaddleHTContourHeight y ε)
        (smoothSaddleHTContourHeight y ε),
      ‖smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
          (smoothSaddleHTSourceExponent beta t)
          (((beta - smoothSaddleHTContourShift y ε : ℝ) : ℂ) +
            (u : ℂ) * Complex.I)‖ ≤ verticalBound) :
    ‖smoothSaddleHTContourEdgeContribution y beta ε t‖ ≤
      smoothSaddleHTContourEdgeSupMajorant y ε
        horizontalBound verticalBound := by
  let left : ℝ := beta - smoothSaddleHTContourShift y ε
  let right : ℝ := smoothSaddleHTContourRight y beta
  let T : ℝ := smoothSaddleHTContourHeight y ε
  let F : ℂ → ℂ := smoothSaddleHTShiftedZetaPerronIntegrand (y : ℝ)
    (smoothSaddleHTSourceExponent beta t)
  have hshiftPos := smoothSaddleHTContourShift_pos hy ε
  have hright := smoothSaddleHTContourRight_gt hy beta
  have hlr : left ≤ right := by
    dsimp [left, right]
    linarith
  have hT : 0 ≤ T := by
    exact (smoothSaddleHTContourHeight_pos y ε).le
  have hbottom' : ‖HIntegral' F left right (-T)‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    simpa [F, T, sub_eq_add_neg] using hbottom x (by simpa [left, right] using hx)
  have htop' : ‖HIntegral' F left right T‖ ≤
      (1 / (2 * Real.pi)) * horizontalBound * (right - left) := by
    apply norm_HIntegral'_le_of_norm_le_const hlr
    intro x hx
    exact htop x (by simpa [left, right] using hx)
  have hleft' : ‖VIntegral' F left (-T) T‖ ≤
      (1 / (2 * Real.pi)) * verticalBound * (2 * T) := by
    have hraw := norm_VIntegral'_le_of_norm_le_const
      (f := F) (line := left) (bottom := -T) (top := T)
      (by linarith) (fun u hu => by
        exact hleft u (by simpa [left, T] using hu))
    convert hraw using 1
    ring
  unfold smoothSaddleHTContourEdgeContribution
  change ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
      VIntegral' F left (-T) T‖ ≤ _
  calc
    ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
        VIntegral' F left (-T) T‖ ≤
      ‖HIntegral' F left right (-T)‖ +
        ‖HIntegral' F left right T‖ +
          ‖VIntegral' F left (-T) T‖ := by
            simpa using (norm_add₃_le :
              ‖-HIntegral' F left right (-T) + HIntegral' F left right T +
                  VIntegral' F left (-T) T‖ ≤
                ‖-HIntegral' F left right (-T)‖ +
                  ‖HIntegral' F left right T‖ +
                    ‖VIntegral' F left (-T) T‖)
    _ ≤ (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
        (1 / (2 * Real.pi)) * horizontalBound * (right - left) +
          (1 / (2 * Real.pi)) * verticalBound * (2 * T) := by
            gcongr
    _ = smoothSaddleHTContourEdgeSupMajorant y ε
        horizontalBound verticalBound := by
      rw [show right - left =
          smoothSaddleHTContourShift y ε + 1 / Real.log y by
        simpa [left, right] using
          smoothSaddleHTContour_horizontal_length y beta ε]
      simp only [T, smoothSaddleHTContourEdgeSupMajorant]
      ring

end

end Tao2026
