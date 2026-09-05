import GafniTao.Pintz2023MellinVertical

/-!
# Pintz (2023), Lemma 3.4: completed Mellin shift

The finite rectangle is taken to infinite height.  Both horizontal edges
vanish, while absolute integrability identifies the two vertical limits.
This gives the exact residue identity behind Pintz's equation (3.5), with
the removable singularity at `w = 0` retained in the left contour.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators Interval

namespace GafniTao

noncomputable section

private lemma tendsto_pintz2023Mellin_rectangle
    {N : ℕ} {s : ℂ} (hN : 0 < N)
    (hsLower : 1 / 4 ≤ s.re) (hsUpper : s.re < 1) :
    Tendsto (fun R : ℝ =>
      RectangleIntegral' (pintz2023MellinContourIntegrand N s)
        (((0 : ℝ) : ℂ) - (R : ℂ) * I)
        (((2 : ℝ) : ℂ) + (R : ℂ) * I)) atTop
      (nhds (
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ u : ℝ, pintz2023MellinContourIntegrand N s
            (((2 : ℝ) : ℂ) + (u : ℂ) * I))) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ u : ℝ, pintz2023MellinContourIntegrand N s
            ((u : ℂ) * I))))) := by
  let f : ℂ → ℂ := pintz2023MellinContourIntegrand N s
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hBottom : Tendsto (fun R : ℝ => HIntegral' f 0 2 (-R))
      atTop (nhds 0) := by
    simpa [f] using tendsto_pintz2023Mellin_HIntegral'_neg_zero hN hsLower
  have hTop : Tendsto (fun R : ℝ => HIntegral' f 0 2 R)
      atTop (nhds 0) := by
    simpa [f] using tendsto_pintz2023Mellin_HIntegral'_zero hN hsLower
  have hRightInt : Integrable (fun u : ℝ =>
      f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
    have hsNonneg : 0 ≤ s.re := by linarith
    simpa [f] using integrable_pintz2023MellinContourIntegrand_right
      hN hsNonneg
  have hLeftInt : Integrable (fun u : ℝ => f ((u : ℂ) * I)) := by
    simpa [f] using integrable_pintz2023MellinContourIntegrand_left
      hN hsLower hsUpper
  have hRight : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R,
        f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) atTop
      (nhds (c * (∫ u : ℝ,
        f (((2 : ℝ) : ℂ) + (u : ℂ) * I)))) :=
    (intervalIntegral_tendsto_integral hRightInt
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hLeft : Tendsto (fun R : ℝ =>
      c * ∫ u in (-R)..R, f ((u : ℂ) * I)) atTop
      (nhds (c * (∫ u : ℝ, f ((u : ℂ) * I)))) :=
    (intervalIntegral_tendsto_integral hLeftInt
      tendsto_neg_atTop_atBot tendsto_id).const_mul c
  have hEdges := (hBottom.sub hTop).add (hRight.sub hLeft)
  have hExpanded : Tendsto (fun R : ℝ =>
      HIntegral' f 0 2 (-R) - HIntegral' f 0 2 R +
        ((c * ∫ u in (-R)..R,
          f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) -
        (c * ∫ u in (-R)..R, f ((u : ℂ) * I)))) atTop
      (nhds (c * (∫ u : ℝ,
          f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((u : ℂ) * I)))) := by
    simpa only [zero_sub, neg_zero, zero_add] using hEdges
  have hRectangle : Tendsto (fun R : ℝ =>
      RectangleIntegral' f
        (((0 : ℝ) : ℂ) - (R : ℂ) * I)
        (((2 : ℝ) : ℂ) + (R : ℂ) * I)) atTop
      (nhds (c * (∫ u : ℝ,
          f (((2 : ℝ) : ℂ) + (u : ℂ) * I)) -
        c * (∫ u : ℝ, f ((u : ℂ) * I)))) := by
    refine hExpanded.congr' ?_
    filter_upwards with R
    rw [pintz2023_RectangleIntegral'_eq_edges]
    simp [c, mul_comm]
    ring
  simpa [f, c] using hRectangle

/-- Exact infinite-line form of Pintz's contour shift. -/
theorem pintz2023SmoothedZetaSum_eq_left_contour_add_residue
    {N : ℕ} {s : ℂ} (hN : 0 < N)
    (hsLower : 1 / 4 ≤ s.re) (hsUpper : s.re < 1) :
    pintz2023SmoothedZetaSum N s =
      pintz2023MellinWeight N (1 - s) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u : ℝ, pintz2023MellinContourIntegrand N s
            ((u : ℂ) * I)) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let right : ℂ := c * ∫ u : ℝ,
    pintz2023MellinContourIntegrand N s
      (((2 : ℝ) : ℂ) + (u : ℂ) * I)
  let left : ℂ := c * ∫ u : ℝ,
    pintz2023MellinContourIntegrand N s ((u : ℂ) * I)
  have hLimit : Tendsto (fun R : ℝ =>
      RectangleIntegral' (pintz2023MellinContourIntegrand N s)
        (((0 : ℝ) : ℂ) - (R : ℂ) * I)
        (((2 : ℝ) : ℂ) + (R : ℂ) * I)) atTop
      (nhds (right - left)) := by
    simpa [right, left, c] using
      tendsto_pintz2023Mellin_rectangle hN hsLower hsUpper
  have hEventually : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' (pintz2023MellinContourIntegrand N s)
        (((0 : ℝ) : ℂ) - (R : ℂ) * I)
        (((2 : ℝ) : ℂ) + (R : ℂ) * I) =
          pintz2023MellinWeight N (1 - s) := by
    filter_upwards [eventually_gt_atTop |s.im|] with R hR
    exact pintz2023Mellin_finite_rectangle hN (by linarith) hsUpper hR
  have hResidueLimit : Tendsto (fun R : ℝ =>
      RectangleIntegral' (pintz2023MellinContourIntegrand N s)
        (((0 : ℝ) : ℂ) - (R : ℂ) * I)
        (((2 : ℝ) : ℂ) + (R : ℂ) * I)) atTop
      (nhds (pintz2023MellinWeight N (1 - s))) :=
    (tendsto_const_nhds.congr'
      (hEventually.mono fun _ h => h.symm))
  have hShift : right - left = pintz2023MellinWeight N (1 - s) :=
    tendsto_nhds_unique hLimit hResidueLimit
  have hRight : pintz2023SmoothedZetaSum N s = right := by
    have hsNonneg : 0 ≤ s.re := by linarith
    simpa [right, c] using
      pintz2023SmoothedZetaSum_eq_right_contour hN hsNonneg
  rw [hRight]
  dsimp only [right, left, c] at hShift ⊢
  linear_combination hShift

#print axioms pintz2023SmoothedZetaSum_eq_left_contour_add_residue

end

end GafniTao
