import Dubon2026.GammaRatioPhase
import Mathlib.Analysis.Calculus.MeanValue

/-! # Exact horizontal log-modulus control for the genuine Gamma function -/

namespace Dubon2026

open Complex Set RiemannZeta.GuthMaynard

noncomputable section

/-- The real logarithm of the actual Gamma modulus at a fixed imaginary height. -/
def gammaHorizontalLogNorm (t u : ℝ) : ℝ := Real.log ‖Gamma (gammaVerticalPoint u t)‖

/-- Along the horizontal variable, the actual Gamma values have digamma as their logarithmic rate. -/
theorem hasDerivAt_gammaHorizontal {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasDerivAt (fun v : ℝ => Gamma (gammaVerticalPoint v t))
      (digamma (gammaVerticalPoint u t) * Gamma (gammaVerticalPoint u t)) u := by
  have hi : HasDerivAt (fun v : ℂ => v + (t : ℂ) * I) 1 (u : ℂ) := by
    simpa using (hasDerivAt_id (u : ℂ)).add_const ((t : ℂ) * I)
  have hh := ((hasDerivAt_Gamma_eq_mul_digamma_of_re_pos
    (show 0 < (gammaVerticalPoint u t).re by simpa only [gammaVerticalPoint_re] using hu)).comp
      (u : ℂ) hi).comp_ofReal
  convert hh using 1
  ring

/-- The horizontal derivative of the true Gamma log-modulus is the real part of the actual digamma function. -/
theorem hasDerivAt_gammaHorizontalLogNorm {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasDerivAt (gammaHorizontalLogNorm t) (digamma (gammaVerticalPoint u t)).re u := by
  have hn : Gamma (gammaVerticalPoint u t) ≠ 0 := Gamma_ne_zero_of_re_pos
    (by simpa only [gammaVerticalPoint_re] using hu)
  have hh := (hasDerivAt_norm_of_complex_rate (hasDerivAt_gammaHorizontal hu t) hn).log
    (norm_ne_zero_iff.mpr hn)
  convert hh using 1
  exact (mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hn)).symm

/-- The literal difference of Gamma log-moduli has the exact leading horizontal power and an explicit inverse-height error. -/
theorem abs_gammaHorizontalLogNorm_sub_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 ≤ t) :
    |(gammaHorizontalLogNorm t a - gammaHorizontalLogNorm t b) - (a - b) * Real.log t| ≤
      ((4 + max a b) / t) * |a - b| := by
  let F : ℝ → ℝ := fun u => gammaHorizontalLogNorm t u - u * Real.log t
  let F' : ℝ → ℝ := fun u => (digamma (gammaVerticalPoint u t)).re - Real.log t
  have hpos (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : 0 < u :=
    (lt_min ha hb).trans_le hu.1
  have hder (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : HasDerivAt F (F' u) u := by
    convert (hasDerivAt_gammaHorizontalLogNorm (hpos u hu) t).sub
      ((hasDerivAt_id u).mul_const (Real.log t)) using 1
    simp [F']
  have hbound (u : ℝ) (hu : u ∈ Icc (min a b) (max a b)) : ‖F' u‖ ≤ (4 + max a b) / t := by
    have hh := TaoTrudgianYang2025.abs_re_digamma_sub_log_im_le
      (z := gammaVerticalPoint u t) (by simpa only [gammaVerticalPoint_re] using hpos u hu)
      (by simpa only [gammaVerticalPoint_im, abs_of_nonneg (by linarith : 0 ≤ t)] using ht)
    have hh' : |F' u| ≤ (4 + u) / t := by
      simpa only [F', gammaVerticalPoint_re, gammaVerticalPoint_im,
        abs_of_nonneg (by linarith : 0 ≤ t)] using hh
    have hn : ‖F' u‖ ≤ (4 + u) / t := by simpa only [Real.norm_eq_abs] using hh'
    exact hn.trans
      (div_le_div_of_nonneg_right (by linarith [hu.2]) (by linarith))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hder u hu).hasDerivWithinAt) hbound (convex_Icc (min a b) (max a b))
    (show b ∈ Icc (min a b) (max a b) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (show a ∈ Icc (min a b) (max a b) from ⟨min_le_left _ _, le_max_left _ _⟩)
  have he : F a - F b = (gammaHorizontalLogNorm t a - gammaHorizontalLogNorm t b) -
      (a - b) * Real.log t := by dsimp [F]; ring
  simpa only [he, Real.norm_eq_abs] using hh

end
end Dubon2026
