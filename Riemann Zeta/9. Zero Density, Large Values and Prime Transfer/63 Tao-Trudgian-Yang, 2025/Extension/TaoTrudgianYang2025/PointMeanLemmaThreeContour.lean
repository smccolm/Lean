import TaoTrudgianYang2025.PointMeanReflection
import TaoTrudgianYang2025.PointMeanLemmaThreeStatement

/-!
Adapted from the adjacent Gafni--Tao development, using the literal target
critical-line zeta norm and the local contour and Gamma-kernel proofs.

# The finite contour in Heath--Brown's Lemma 3

This file fixes the literal source rectangle: horizontal displacement
`delta = 1 / log t` and vertical radius `(log t)^2`.  The residue is the
actual square of zeta at the critical-line point.  The four oriented edges
are exposed separately for the quantitative estimates.
-/

open Complex Set MeasureTheory
open scoped Interval

namespace TaoTrudgianYang2025

noncomputable section

open RiemannZeta.GuthMaynard

private theorem exp_two_le_eight_heathBrown : Real.exp 2 ≤ 8 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

theorem two_lt_log_of_ten_le {t : ℝ} (ht : 10 ≤ t) :
    2 < Real.log t := by
  rw [Real.lt_log_iff_exp_lt (by linarith : 0 < t)]
  exact exp_two_le_eight_heathBrown.trans_lt (by linarith)

/-- Source parameters used by the Lemma-3 residue rectangle. -/
noncomputable def heathBrownLemmaThreeDelta (t : ℝ) : ℝ :=
  1 / Real.log t

noncomputable def heathBrownLemmaThreeRadius (t : ℝ) : ℝ :=
  Real.log t ^ (2 : ℕ)

theorem heathBrownLemmaThreeDelta_pos {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeDelta t := by
  unfold heathBrownLemmaThreeDelta
  have := two_lt_log_of_ten_le ht
  positivity

theorem heathBrownLemmaThreeDelta_lt_half {t : ℝ} (ht : 10 ≤ t) :
    heathBrownLemmaThreeDelta t < 1 / 2 := by
  unfold heathBrownLemmaThreeDelta
  exact one_div_lt_one_div_of_lt (by norm_num) (two_lt_log_of_ten_le ht)

theorem heathBrownLemmaThreeRadius_pos {t : ℝ} (ht : 10 ≤ t) :
    0 < heathBrownLemmaThreeRadius t := by
  unfold heathBrownLemmaThreeRadius
  exact sq_pos_of_pos (by linarith [two_lt_log_of_ten_le ht])

/-- The exact residue identity used in the proof of Heath--Brown Lemma 3. -/
theorem heathBrownLemmaThree_finiteRectangle (t : ℝ) (ht : 10 ≤ t) :
    RectangleIntegral'
        (heathBrownZetaSquareMellinIntegrand
          (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))
        (((-heathBrownLemmaThreeDelta t : ℝ) : ℂ) -
          (heathBrownLemmaThreeRadius t : ℂ) * I)
        (((heathBrownLemmaThreeDelta t : ℝ) : ℂ) +
          (heathBrownLemmaThreeRadius t : ℂ) * I) =
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let delta : ℝ := heathBrownLemmaThreeDelta t
  let H : ℝ := heathBrownLemmaThreeRadius t
  have hdelta : 0 < delta := heathBrownLemmaThreeDelta_pos ht
  have hdeltaHalf : delta < 1 / 2 := heathBrownLemmaThreeDelta_lt_half ht
  have hH : 0 < H := heathBrownLemmaThreeRadius_pos ht
  have hpRe : (heathBrownMovingPole s).re = 1 / 2 := by
    simp [heathBrownMovingPole, s]
    ring
  have hrect := heathBrown_gammaPole_finite_rectangle
    (s := s) (delta := delta) (d := delta) (H := H)
    hdelta (hdeltaHalf.trans (by norm_num)) hdelta
    (by rw [hpRe]; exact hdeltaHalf) hH
  simpa only [s, delta, H, ofReal_neg] using hrect

/-- Expansion of the normalized source rectangle into its two horizontal
and two vertical edges, retaining their orientations. -/
theorem heathBrownLemmaThree_rectangle_eq_edges (t : ℝ) :
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
    let delta : ℝ := heathBrownLemmaThreeDelta t
    let H : ℝ := heathBrownLemmaThreeRadius t
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        (((-delta : ℝ) : ℂ) - (H : ℂ) * I)
        (((delta : ℝ) : ℂ) + (H : ℂ) * I) =
      HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta (-H) -
        HIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) delta H +
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) delta (-H) H -
        VIntegral' (heathBrownZetaSquareMellinIntegrand s) (-delta) (-H) H := by
  dsimp only
  unfold RectangleIntegral' RectangleIntegral HIntegral' VIntegral'
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
  ring


end

end TaoTrudgianYang2025
