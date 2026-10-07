import Dubon2026.TrigammaAsymptotic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform horizontal variation of actual digamma at positive real part -/

namespace Dubon2026

open Complex Set RiemannZeta.GuthMaynard

noncomputable section

/-- The proved reciprocal trigamma approximation bounds the actual derivative uniformly across the right half-plane. -/
theorem norm_deriv_digamma_le_of_im_ge_one {z : ℂ} (hz : 0 < z.re) (ht : 1 ≤ z.im) :
    ‖deriv digamma z‖ ≤ 33 / z.im := by
  have ht0 : 0 < z.im := by linarith
  have he := norm_deriv_digamma_sub_inv_le hz (by simpa only [abs_of_pos ht0] using ht)
  rw [abs_of_pos ht0] at he
  have hi : ‖z⁻¹‖ ≤ 1 / z.im := by
    rw [norm_inv, one_div]
    exact inv_anti₀ ht0 (by simpa only [abs_of_pos ht0] using Complex.abs_im_le_norm z)
  have hq : 32 / z.im ^ 2 ≤ 32 / z.im :=
    div_le_div_of_nonneg_left (by norm_num) ht0 (by nlinarith)
  calc
    ‖deriv digamma z‖ = ‖(deriv digamma z - z⁻¹) + z⁻¹‖ := by rw [sub_add_cancel]
    _ ≤ ‖deriv digamma z - z⁻¹‖ + ‖z⁻¹‖ := norm_add_le _ _
    _ ≤ 32 / z.im + 1 / z.im := add_le_add (he.trans hq) hi
    _ = 33 / z.im := by ring

/-- The actual digamma difference between any two positive real shifts has a uniform inverse-height bound. -/
theorem norm_digamma_horizontal_sub_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 ≤ t) :
    ‖digamma ((a : ℂ) + t * I) - digamma ((b : ℂ) + t * I)‖ ≤ (33 / t) * |a - b| := by
  let F : ℝ → ℂ := fun u => digamma ((u : ℂ) + t * I)
  let F' : ℝ → ℂ := fun u => deriv digamma ((u : ℂ) + t * I)
  have hpos (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : 0 < u :=
    (lt_min ha hb).trans_le hu.1
  have hder (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : HasDerivAt F (F' u) u := by
    have hp := (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one
      (z := (u : ℂ) + t * I) (by simpa using hpos u hu)).differentiableAt.hasDerivAt
    have hi : HasDerivAt (fun v : ℂ => v + (t : ℂ) * I) 1 (u : ℂ) := by
      simpa using (hasDerivAt_id (u : ℂ)).add_const ((t : ℂ) * I)
    simpa only [mul_one] using (hp.comp (u : ℂ) hi).comp_ofReal
  have hbound (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : ‖F' u‖ ≤ 33 / t := by
    simpa only [F', add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] using
      norm_deriv_digamma_le_of_im_ge_one (z := (u : ℂ) + t * I)
        (by simpa using hpos u hu) (by simpa using ht)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hder u hu).hasDerivWithinAt) hbound (convex_Icc (min a b) (max a b))
    (show b ∈ Icc (min a b) (max a b) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (show a ∈ Icc (min a b) (max a b) from ⟨min_le_left _ _, le_max_left _ _⟩)
  simpa only [F, Real.norm_eq_abs] using hh

end
end Dubon2026
