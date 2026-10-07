import Dubon2026.NewmanKernel
import GuthMaynardExternal.PNT.ResidueCalcOnRectangles

/-! # Cauchy identities for the actual analytic Tauberian rectangle kernel -/

namespace Dubon2026

open Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Cauchy's formula on a rectangle, derived from the existing simple-pole residue theorem. -/
theorem newman_rectangle_cauchy {F : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h0 : Rectangle z w ∈ 𝓝 (0 : ℂ)) (hF : DifferentiableOn ℂ F (Rectangle z w)) :
    RectangleIntegral' (fun s => F s / s) z w = F 0 := by
  apply ResidueTheoremOnRectangleWithSimplePole hre him h0
    ((Complex.differentiableOn_dslope h0).mpr hF)
  intro s hs
  have hs0 : s ≠ 0 := hs.2
  simp only [Pi.sub_apply, sub_zero, dslope_of_ne F hs0, slope_def_field]
  ring

/-- The exact weighted contour integrand used in analytic Tauberian inversion. -/
def newmanContourIntegrand (G : ℂ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  G z * Complex.exp ((T : ℂ) * z) * newmanKernel R z

/-- Its numerator is holomorphic wherever the supplied genuine continuation is holomorphic. -/
theorem differentiableOn_newmanNumerator {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (T R : ℝ) :
    DifferentiableOn ℂ (fun z => G z * Complex.exp ((T : ℂ) * z) *
      (1 + z ^ 2 / (R : ℂ) ^ 2)) U := by
  apply (hG.mul (by fun_prop)).mul
  fun_prop

/-- The weighted rectangle integral is exactly the continuation's value at the origin. -/
theorem newman_rectangle_formula {G : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h0 : Rectangle z w ∈ 𝓝 (0 : ℂ))
    (hG : DifferentiableOn ℂ G (Rectangle z w)) (T R : ℝ) :
    RectangleIntegral' (newmanContourIntegrand G T R) z w = G 0 := by
  have hh := newman_rectangle_cauchy hre him h0 (differentiableOn_newmanNumerator hG T R)
  simpa only [newmanContourIntegrand, newmanKernel, mul_div_assoc, mul_zero,
    Complex.exp_zero, mul_one, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] using hh

/-- The three oriented edges on the right of the imaginary axis. -/
def newmanRightContour (F : ℂ → ℂ) (R : ℝ) : ℂ :=
  HIntegral F 0 R (-R) - HIntegral F 0 R R + VIntegral F R (-R) R

/-- The three oriented edges on the left of the imaginary axis. -/
def newmanLeftContour (F : ℂ → ℂ) (d R : ℝ) : ℂ :=
  HIntegral F (-d) 0 (-R) - HIntegral F (-d) 0 R - VIntegral F (-d) (-R) R

/-- Splitting the actual horizontal integrals gives the two half-contours without an artificial central edge. -/
theorem newman_rectangle_split {F : ℂ → ℂ} {d R : ℝ} (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hi : RectangleBorderIntegrable F ((-d : ℂ) - R * I) ((R : ℂ) + R * I)) :
    RectangleIntegral F ((-d : ℂ) - R * I) ((R : ℂ) + R * I) =
      newmanRightContour F R + newmanLeftContour F d R := by
  have hb : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (-R : ℝ) * I)) volume (-d) R := by
    simpa using hi.1
  have ht : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + R * I)) volume (-d) R := by
    simpa using hi.2.1
  have hz : (0 : ℝ) ∈ uIcc (-d) R := by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hR⟩
  have hb' := intervalIntegral.integral_add_adjacent_intervals
    (hb.mono_set (uIcc_subset_uIcc_left hz)) (hb.mono_set (uIcc_subset_uIcc_right hz))
  have ht' := intervalIntegral.integral_add_adjacent_intervals
    (ht.mono_set (uIcc_subset_uIcc_left hz)) (ht.mono_set (uIcc_subset_uIcc_right hz))
  simp only [RectangleIntegral, newmanRightContour, newmanLeftContour, HIntegral,
    sub_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, add_re, add_zero, sub_im, neg_im, mul_im, zero_add, neg_zero, zero_sub, add_im,
    ofReal_neg] at *
  rw [← hb', ← ht']
  abel

end
end Dubon2026
