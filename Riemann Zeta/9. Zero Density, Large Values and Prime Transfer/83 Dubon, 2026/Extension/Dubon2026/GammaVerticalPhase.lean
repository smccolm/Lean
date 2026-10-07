import TaoTrudgianYang2025.ZetaSquareGammaPhase

/-! # The genuine vertical Gamma phase and its logarithmic frequency -/

namespace Dubon2026

open Complex RiemannZeta.GuthMaynard
open scoped ComplexConjugate

noncomputable section

/-- A literal point on a vertical line in the Gamma right half-plane. -/
def gammaVerticalPoint (a t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * I

/-- The exact reflected Gamma phase, normalized by conjugate values of Gamma. -/
def gammaVerticalPhase (a t : ℝ) : ℂ :=
  Gamma (gammaVerticalPoint a (-t)) / Gamma (gammaVerticalPoint a t)

/-- The real frequency obtained from the actual Gamma logarithmic derivative. -/
def gammaVerticalFrequency (a t : ℝ) : ℝ := -2 * (digamma (gammaVerticalPoint a t)).re

/-- Reflection of the true vertical point is complex conjugation. -/
theorem gammaVerticalPoint_neg (a t : ℝ) : gammaVerticalPoint a (-t) = conj (gammaVerticalPoint a t) := by
  simp [gammaVerticalPoint]

/-- The real coordinate is precisely the fixed vertical-line parameter. -/
theorem gammaVerticalPoint_re (a t : ℝ) : (gammaVerticalPoint a t).re = a := by
  simp [gammaVerticalPoint]

/-- The imaginary coordinate is precisely the actual height. -/
theorem gammaVerticalPoint_im (a t : ℝ) : (gammaVerticalPoint a t).im = t := by
  simp [gammaVerticalPoint]

/-- The genuine reflected phase has unit modulus on every positive vertical line. -/
theorem norm_gammaVerticalPhase {a : ℝ} (ha : 0 < a) (t : ℝ) : ‖gammaVerticalPhase a t‖ = 1 := by
  rw [gammaVerticalPhase, gammaVerticalPoint_neg, Gamma_conj, norm_div, norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (by simpa [gammaVerticalPoint] using ha))

/-- The actual Gamma values along the vertical line satisfy their exact complex differential equation. -/
theorem hasDerivAt_gammaVertical {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Gamma (gammaVerticalPoint a u))
      (Gamma (gammaVerticalPoint a t) * digamma (gammaVerticalPoint a t) * I) t := by
  have hi : HasDerivAt (fun z : ℂ => (a : ℂ) + z * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (a : ℂ)
  exact ((hasDerivAt_Gamma_eq_mul_digamma_of_re_pos
    (by simpa [gammaVerticalPoint] using ha)).comp (t : ℂ) hi).comp_ofReal

/-- The derivative of the actual phase is i times its proved real frequency times the phase itself. -/
theorem hasDerivAt_gammaVerticalPhase {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (gammaVerticalPhase a)
      (I * (gammaVerticalFrequency a t : ℂ) * gammaVerticalPhase a t) t := by
  have hm := (hasDerivAt_gammaVertical ha (-t)).scomp t (hasDerivAt_neg t)
  have hp := hasDerivAt_gammaVertical ha t
  have hn := Gamma_ne_zero_of_re_pos (show 0 < (gammaVerticalPoint a t).re by
    simpa only [gammaVerticalPoint_re] using ha)
  have he : digamma (gammaVerticalPoint a (-t)) + digamma (gammaVerticalPoint a t) =
      2 * ((digamma (gammaVerticalPoint a t)).re : ℂ) := by
    rw [gammaVerticalPoint_neg, TaoTrudgianYang2025.digamma_conj, add_comm, Complex.add_conj]
    push_cast
    rfl
  convert hm.div hp hn using 1
  unfold gammaVerticalFrequency gammaVerticalPhase
  simp only [Function.comp_apply, neg_smul, one_smul]
  push_cast
  field_simp
  linear_combination Gamma (gammaVerticalPoint a (-t)) * he

/-- The actual phase frequency has a uniform logarithmic approximation with explicit vertical error. -/
theorem abs_gammaVerticalFrequency_add_log_le {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ |t|) :
    |gammaVerticalFrequency a t + 2 * Real.log (|t|)| ≤ 2 * (4 + a) / |t| := by
  have hh := TaoTrudgianYang2025.abs_re_digamma_sub_log_im_le
    (z := gammaVerticalPoint a t) (by simpa [gammaVerticalPoint] using ha)
    (by simpa only [gammaVerticalPoint_im] using ht)
  rw [gammaVerticalPoint_re, gammaVerticalPoint_im] at hh
  have he : gammaVerticalFrequency a t + 2 * Real.log |t| =
      -2 * ((digamma (gammaVerticalPoint a t)).re - Real.log |t|) := by
    unfold gammaVerticalFrequency
    ring
  rw [he, abs_mul]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ((4 + a) / |t|) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

end
end Dubon2026
