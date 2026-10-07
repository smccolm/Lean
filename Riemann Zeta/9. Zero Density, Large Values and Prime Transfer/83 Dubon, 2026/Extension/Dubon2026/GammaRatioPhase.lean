import Dubon2026.NormalizedComplexPhase
import Dubon2026.GammaPhaseCurvature

/-! # The exact normalized phase of a reflected Gamma ratio with unequal real shifts -/

namespace Dubon2026

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The genuine reflected Gamma ratio with independent positive real shifts. -/
def reflectedGammaRatio (a b t : ℝ) : ℂ :=
  Gamma (gammaVerticalPoint a (-t)) / Gamma (gammaVerticalPoint b t)

/-- The actual unit-modulus part of the reflected Gamma ratio. -/
def gammaRatioPhase (a b t : ℝ) : ℂ :=
  reflectedGammaRatio a b t / (‖reflectedGammaRatio a b t‖ : ℂ)

/-- The real phase frequency, expressed by the already proved actual digamma frequencies. -/
def gammaRatioFrequency (a b t : ℝ) : ℝ :=
  (gammaVerticalFrequency a t + gammaVerticalFrequency b t) / 2

/-- The actual reflected Gamma ratio is nonzero for positive real shifts. -/
theorem reflectedGammaRatio_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    reflectedGammaRatio a b t ≠ 0 :=
  div_ne_zero (Gamma_ne_zero_of_re_pos (by simpa only [gammaVerticalPoint_re] using ha))
    (Gamma_ne_zero_of_re_pos (by simpa only [gammaVerticalPoint_re] using hb))

/-- Normalization of the literal Gamma quotient has exactly unit modulus. -/
theorem norm_gammaRatioPhase {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖gammaRatioPhase a b t‖ = 1 :=
  norm_normalized_complex_phase (reflectedGammaRatio_ne_zero ha hb t)

/-- The genuine reflected Gamma ratio satisfies its exact complex logarithmic differential equation. -/
theorem hasDerivAt_reflectedGammaRatio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    HasDerivAt (reflectedGammaRatio a b)
      ((-I * (digamma (gammaVerticalPoint a (-t)) + digamma (gammaVerticalPoint b t))) *
        reflectedGammaRatio a b t) t := by
  have hm := (hasDerivAt_gammaVertical ha (-t)).scomp t (hasDerivAt_neg t)
  have hp := hasDerivAt_gammaVertical hb t
  have hn := Gamma_ne_zero_of_re_pos (show 0 < (gammaVerticalPoint b t).re by
    simpa only [gammaVerticalPoint_re] using hb)
  convert hm.div hp hn using 1
  simp only [reflectedGammaRatio, Function.comp_apply, neg_smul, one_smul]
  field_simp
  ring

/-- The actual normalized Gamma ratio has the precise real-frequency phase equation. -/
theorem hasDerivAt_gammaRatioPhase {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    HasDerivAt (gammaRatioPhase a b)
      (I * (gammaRatioFrequency a b t : ℂ) * gammaRatioPhase a b t) t := by
  have hi : (-I * (digamma (gammaVerticalPoint a (-t)) + digamma (gammaVerticalPoint b t))).im =
      gammaRatioFrequency a b t := by
    rw [gammaVerticalPoint_neg, TaoTrudgianYang2025.digamma_conj]
    simp only [mul_im, I_re, zero_mul, neg_im, I_im, neg_mul,
      one_mul, zero_add, add_re, conj_re, gammaRatioFrequency, gammaVerticalFrequency]
    ring
  simpa only [gammaRatioPhase, hi] using hasDerivAt_normalized_complex_phase
    (hasDerivAt_reflectedGammaRatio ha hb t) (reflectedGammaRatio_ne_zero ha hb t)

/-- The true Gamma quotient modulus has its exact derivative, needed for the oscillatory amplitude variation. -/
theorem hasDerivAt_norm_reflectedGammaRatio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    HasDerivAt (fun u => ‖reflectedGammaRatio a b u‖)
      (((digamma (gammaVerticalPoint b t)).im - (digamma (gammaVerticalPoint a t)).im) *
        ‖reflectedGammaRatio a b t‖) t := by
  have hr : (-I * (digamma (gammaVerticalPoint a (-t)) + digamma (gammaVerticalPoint b t))).re =
      (digamma (gammaVerticalPoint b t)).im - (digamma (gammaVerticalPoint a t)).im := by
    rw [gammaVerticalPoint_neg, TaoTrudgianYang2025.digamma_conj]
    simp
    ring
  simpa only [hr] using hasDerivAt_norm_of_complex_rate
    (hasDerivAt_reflectedGammaRatio ha hb t) (reflectedGammaRatio_ne_zero ha hb t)

/-- The actual quotient is exactly its positive modulus times the actual normalized phase. -/
theorem reflectedGammaRatio_eq_norm_mul_phase {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    reflectedGammaRatio a b t = (‖reflectedGammaRatio a b t‖ : ℂ) * gammaRatioPhase a b t := by
  rw [gammaRatioPhase, mul_div_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (reflectedGammaRatio_ne_zero ha hb t))

end
end Dubon2026
