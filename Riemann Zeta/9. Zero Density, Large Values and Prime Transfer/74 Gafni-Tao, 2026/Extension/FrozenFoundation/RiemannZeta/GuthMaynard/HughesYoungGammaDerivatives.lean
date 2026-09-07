import Mathlib.Analysis.Calculus.MeanValue
import RiemannZeta.GuthMaynard.HughesYoungPolygamma

open Complex Filter Set Topology
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative Gamma-ratio derivative input for Hughes--Young

The paired Gamma quotients in Hughes--Young equation (65) gain their final
inverse height power from cancellation between shifted and unshifted
logarithmic derivatives.  This file begins that cancellation argument with a
uniform mean-value theorem for every positive-order derivative of `digamma`.
-/

/-- The zeroth-order companion to `norm_iteratedDeriv_digamma_sub_le`.
The derivative of `digamma` is the first polygamma series, so a horizontal
or oblique displacement gains one full inverse power of the common
ordinate. -/
theorem norm_digamma_sub_le
    {z₀ z₁ : ℂ} {a Y : ℝ}
    (ha : 0 < a) (hY : 1 ≤ Y)
    (hsegment : ∀ w ∈ segment ℝ z₀ z₁, a ≤ w.re ∧ Y ≤ |w.im|) :
    ‖Complex.digamma z₁ - Complex.digamma z₀‖ ≤
      (2 * (3 + (min a 1)⁻¹ ^ 2) * Y⁻¹) * ‖z₁ - z₀‖ := by
  let C : ℝ := 2 * (3 + (min a 1)⁻¹ ^ 2) * Y⁻¹
  have hdiff (w : ℂ) (hw : w ∈ segment ℝ z₀ z₁) :
      HasDerivWithinAt Complex.digamma
        (hughesYoungPolygammaSeries 1 w) (segment ℝ z₀ z₁) w := by
    exact (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one
      (ha.trans_le (hsegment w hw).1)).hasDerivWithinAt
  have hbound (w : ℂ) (hw : w ∈ segment ℝ z₀ z₁) :
      ‖hughesYoungPolygammaSeries 1 w‖ ≤ C := by
    have hwre : a ≤ w.re := (hsegment w hw).1
    have hwim : Y ≤ |w.im| := (hsegment w hw).2
    have hpos : 0 < w.re := ha.trans_le hwre
    have himOne : 1 ≤ |w.im| := hY.trans hwim
    have hraw := norm_hughesYoungPolygammaSeries_le hpos (j := 1)
      (by omega) himOne
    have hcpos : 0 < min a 1 := lt_min ha zero_lt_one
    have hcmin : min a 1 ≤ min w.re 1 := min_le_min hwre le_rfl
    have hinvC : (min w.re 1)⁻¹ ≤ (min a 1)⁻¹ :=
      inv_anti₀ hcpos hcmin
    have hpowC : (min w.re 1)⁻¹ ^ 2 ≤ (min a 1)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinvC _
    have hinvY : |w.im|⁻¹ ≤ Y⁻¹ :=
      inv_anti₀ (lt_of_lt_of_le zero_lt_one hY) hwim
    have hraw' :
        ‖hughesYoungPolygammaSeries 1 w‖ ≤
          (3 + (min w.re 1)⁻¹ ^ 2) * |w.im|⁻¹ := by
      simpa only [pow_one] using hraw
    refine hraw'.trans ?_
    dsimp [C]
    have hnonneg : 0 ≤ (3 + (min a 1)⁻¹ ^ 2) * Y⁻¹ := by positivity
    calc
      (3 + (min w.re 1)⁻¹ ^ 2) * |w.im|⁻¹ ≤
          (3 + (min a 1)⁻¹ ^ 2) * Y⁻¹ := by gcongr
      _ ≤ 2 * (3 + (min a 1)⁻¹ ^ 2) * Y⁻¹ := by
        nlinarith
  simpa only [C] using
    (convex_segment z₀ z₁).norm_image_sub_le_of_norm_hasDerivWithin_le
      hdiff hbound (left_mem_segment ℝ z₀ z₁) (right_mem_segment ℝ z₀ z₁)

/-- Quantitative difference estimate for positive-order derivatives of
`digamma` along a segment that stays in a fixed right half-plane and away
from the real axis.  It is the exact extra inverse-height gain that is lost
if the two Gamma factors are bounded separately. -/
theorem norm_iteratedDeriv_digamma_sub_le
    {j : ℕ} (hj : 1 ≤ j) {z₀ z₁ : ℂ} {a Y : ℝ}
    (ha : 0 < a) (hY : 1 ≤ Y)
    (hsegment : ∀ w ∈ segment ℝ z₀ z₁, a ≤ w.re ∧ Y ≤ |w.im|) :
    ‖iteratedDeriv j Complex.digamma z₁ -
        iteratedDeriv j Complex.digamma z₀‖ ≤
      ((j + 1).factorial *
          (3 + (min a 1)⁻¹ ^ (j + 2)) * Y⁻¹ ^ (j + 1)) *
        ‖z₁ - z₀‖ := by
  let C : ℝ := (j + 1).factorial *
    (3 + (min a 1)⁻¹ ^ (j + 2)) * Y⁻¹ ^ (j + 1)
  have hdiff (w : ℂ) (hw : w ∈ segment ℝ z₀ z₁) :
      HasDerivWithinAt (iteratedDeriv j Complex.digamma)
        (iteratedDeriv (j + 1) Complex.digamma w)
        (segment ℝ z₀ z₁) w := by
    exact (hasDerivAt_iteratedDeriv_digamma hj
      (ha.trans_le (hsegment w hw).1)).hasDerivWithinAt
  have hbound (w : ℂ) (hw : w ∈ segment ℝ z₀ z₁) :
      ‖iteratedDeriv (j + 1) Complex.digamma w‖ ≤ C := by
    have hwre : a ≤ w.re := (hsegment w hw).1
    have hwim : Y ≤ |w.im| := (hsegment w hw).2
    have hpos : 0 < w.re := ha.trans_le hwre
    have himOne : 1 ≤ |w.im| := hY.trans hwim
    have hraw := norm_iteratedDeriv_digamma_le (j := j + 1) (by omega)
      hpos himOne
    have hcpos : 0 < min a 1 := lt_min ha zero_lt_one
    have hcmin : min a 1 ≤ min w.re 1 := min_le_min hwre le_rfl
    have hinvC : (min w.re 1)⁻¹ ≤ (min a 1)⁻¹ :=
      inv_anti₀ hcpos hcmin
    have hpowC : (min w.re 1)⁻¹ ^ (j + 2) ≤
        (min a 1)⁻¹ ^ (j + 2) :=
      pow_le_pow_left₀ (by positivity) hinvC _
    have hinvY : |w.im|⁻¹ ≤ Y⁻¹ :=
      inv_anti₀ (lt_of_lt_of_le zero_lt_one hY) hwim
    have hpowY : |w.im|⁻¹ ^ (j + 1) ≤ Y⁻¹ ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) hinvY _
    refine hraw.trans ?_
    dsimp [C]
    gcongr
  simpa only [C] using
    (convex_segment z₀ z₁).norm_image_sub_le_of_norm_hasDerivWithin_le
      hdiff hbound (left_mem_segment ℝ z₀ z₁) (right_mem_segment ℝ z₀ z₁)

end RiemannZeta.GuthMaynard
