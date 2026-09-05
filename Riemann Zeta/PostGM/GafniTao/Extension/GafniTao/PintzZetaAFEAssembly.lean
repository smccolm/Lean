import GafniTao.PintzZetaAFEHorizontal

/-!
# Exact two-piece single-zeta AFE

Reflection converts the left side of the completed-xi rectangle based at
`s` into the right side based at `1-s`.  After the two horizontal sides tend
to zero, their sum is exactly `completedXiNumerator s`.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace GafniTao

open RiemannZeta.GuthMaynard

theorem hIntegral_pintzZetaAFE_bottom
    (s : ℂ) (c H : ℝ) :
    HIntegral (pintzZetaAFEContourIntegrand s) (-c) c (-H) =
      -HIntegral (pintzZetaAFEContourIntegrand (1 - s)) (-c) c H := by
  let f : ℂ → ℂ := pintzZetaAFEContourIntegrand s
  let g : ℂ → ℂ := pintzZetaAFEContourIntegrand (1 - s)
  have hpoint : ∀ x : ℝ,
      f (((-x : ℝ) : ℂ) + ((-H : ℝ) : ℂ) * I) =
        -g ((x : ℂ) + (H : ℂ) * I) := by
    intro x
    have harg : (((-x : ℝ) : ℂ) + ((-H : ℝ) : ℂ) * I) =
        -((x : ℂ) + (H : ℂ) * I) := by
      push_cast
      ring
    rw [harg]
    exact pintzZetaAFEContourIntegrand_neg s _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => f ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
    (a := -c) (b := c)
  simp only [neg_neg] at hcomp
  unfold HIntegral
  change (∫ x in -c..c,
      f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
    -∫ x in -c..c, g ((x : ℂ) + (H : ℂ) * I)
  calc
    (∫ x in -c..c,
        f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) =
      ∫ x in -c..c,
        f (((-x : ℝ) : ℂ) + ((-H : ℝ) : ℂ) * I) := by
          simpa only [ofReal_neg] using hcomp.symm
    _ = ∫ x in -c..c, -g ((x : ℂ) + (H : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -∫ x in -c..c, g ((x : ℂ) + (H : ℂ) * I) := by
      rw [intervalIntegral.integral_neg]

theorem vIntegral_pintzZetaAFE_left
    (s : ℂ) (c H : ℝ) :
    VIntegral (pintzZetaAFEContourIntegrand s) (-c) (-H) H =
      -VIntegral (pintzZetaAFEContourIntegrand (1 - s)) c (-H) H := by
  let f : ℂ → ℂ := pintzZetaAFEContourIntegrand s
  let g : ℂ → ℂ := pintzZetaAFEContourIntegrand (1 - s)
  have hpoint : ∀ y : ℝ,
      f (((-c : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) =
        -g ((c : ℂ) + (y : ℂ) * I) := by
    intro y
    have harg : (((-c : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) =
        -((c : ℂ) + (y : ℂ) * I) := by
      push_cast
      ring
    rw [harg]
    exact pintzZetaAFEContourIntegrand_neg s _
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ => f (((-c : ℝ) : ℂ) + (y : ℂ) * I))
    (a := -H) (b := H)
  simp only [neg_neg] at hcomp
  unfold VIntegral
  have hintegral :
      (∫ y in -H..H,
          f (((-c : ℝ) : ℂ) + (y : ℂ) * I)) =
        -∫ y in -H..H, g ((c : ℂ) + (y : ℂ) * I) := by
    calc
      _ = ∫ y in -H..H,
          f (((-c : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
            simpa only [ofReal_neg] using hcomp.symm
      _ = ∫ y in -H..H, -g ((c : ℂ) + (y : ℂ) * I) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact hpoint y
      _ = -∫ y in -H..H, g ((c : ℂ) + (y : ℂ) * I) := by
        rw [intervalIntegral.integral_neg]
  rw [hintegral, smul_neg]

/-- Exact finite-height AFE, with both completed-zeta pieces and both
horizontal remainders displayed. -/
theorem pintzZetaAFE_truncated_native
    (s : ℂ) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    completedXiNumerator s =
      VIntegral' (pintzZetaAFEContourIntegrand s) c (-H) H +
      VIntegral' (pintzZetaAFEContourIntegrand (1 - s)) c (-H) H -
      HIntegral' (pintzZetaAFEContourIntegrand s) (-c) c H -
      HIntegral' (pintzZetaAFEContourIntegrand (1 - s)) (-c) c H := by
  have hrect := pintzZetaAFE_finiteRectangle s hc hH
  have hbottom := hIntegral_pintzZetaAFE_bottom s c H
  have hleft := vIntegral_pintzZetaAFE_left s c H
  unfold RectangleIntegral' RectangleIntegral at hrect
  unfold HIntegral' VIntegral'
  have hrect' :
      (1 / (2 * Real.pi * I)) •
        (HIntegral (pintzZetaAFEContourIntegrand s) (-c) c (-H) -
          HIntegral (pintzZetaAFEContourIntegrand s) (-c) c H +
          VIntegral (pintzZetaAFEContourIntegrand s) c (-H) H -
          VIntegral (pintzZetaAFEContourIntegrand s) (-c) (-H) H) =
        completedXiNumerator s := by
    convert hrect using 1
    all_goals simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
  rw [hbottom, hleft] at hrect'
  rw [← hrect']
  simp only [smul_add, smul_sub, smul_neg]
  abel

/-- Infinite-height two-piece AFE in exact improper-contour form. -/
theorem pintzZetaAFE_vertical_limit_native (s : ℂ) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      VIntegral' (pintzZetaAFEContourIntegrand s) c (-H) H +
      VIntegral' (pintzZetaAFEContourIntegrand (1 - s)) c (-H) H)
      atTop (nhds (completedXiNumerator s)) := by
  have hsTop := tendsto_hIntegral'_pintzZetaAFE_top_zero s c hc.le
  have hrefTop :=
    tendsto_hIntegral'_pintzZetaAFE_top_zero (1 - s) c hc.le
  have htarget : Tendsto (fun H : ℝ =>
      completedXiNumerator s +
        HIntegral' (pintzZetaAFEContourIntegrand s) (-c) c H +
        HIntegral' (pintzZetaAFEContourIntegrand (1 - s)) (-c) c H)
      atTop (nhds (completedXiNumerator s)) := by
    simpa using (tendsto_const_nhds.add hsTop).add hrefTop
  apply htarget.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hfinite := pintzZetaAFE_truncated_native s hc hH
  linear_combination hfinite

#print axioms hIntegral_pintzZetaAFE_bottom
#print axioms vIntegral_pintzZetaAFE_left
#print axioms pintzZetaAFE_truncated_native
#print axioms pintzZetaAFE_vertical_limit_native

end GafniTao
