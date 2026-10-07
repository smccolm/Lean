import Dubon2026.GammaRatioCurvature
import Dubon2026.PhaseSecondDerivative

/-! # Uniform oscillation for the actual normalized product of two shifted Gamma ratios -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The genuine normalized product of two reflected Gamma ratios with arbitrary linear modulation. -/
def doubleGammaOscillatoryPhase (a b c d v t : ℝ) : ℂ :=
  Complex.exp (I * ((v * t : ℝ) : ℂ)) * gammaRatioPhase a b t * gammaRatioPhase c d t

/-- The actual real frequency of the shifted two-ratio phase. -/
def doubleGammaFrequency (a b c d v t : ℝ) : ℝ :=
  v + gammaRatioFrequency a b t + gammaRatioFrequency c d t

/-- The exact shifted two-ratio phase has unit modulus. -/
theorem norm_doubleGammaOscillatoryPhase {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (v t : ℝ) :
    ‖doubleGammaOscillatoryPhase a b c d v t‖ = 1 := by
  simp [doubleGammaOscillatoryPhase, Complex.norm_exp, norm_gammaRatioPhase ha hb,
    norm_gammaRatioPhase hc hd]

/-- The genuine normalized shifted Gamma product satisfies its exact phase differential equation. -/
theorem hasDerivAt_doubleGammaOscillatoryPhase {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (v t : ℝ) :
    HasDerivAt (doubleGammaOscillatoryPhase a b c d v)
      (I * (doubleGammaFrequency a b c d v t : ℂ) * doubleGammaOscillatoryPhase a b c d v t) t := by
  have he := ((((hasDerivAt_id t).const_mul v).ofReal_comp).const_mul I).cexp
  convert (he.mul (hasDerivAt_gammaRatioPhase ha hb t)).mul
    (hasDerivAt_gammaRatioPhase hc hd t) using 1
  simp only [doubleGammaOscillatoryPhase, doubleGammaFrequency, ofReal_add, id_eq, mul_one, Pi.mul_apply]
  ring

/-- The actual product frequency is differentiable, with the exact sum of both ratio curvatures. -/
theorem hasDerivAt_doubleGammaFrequency {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (v t : ℝ) :
    HasDerivAt (doubleGammaFrequency a b c d v)
      (deriv (gammaRatioFrequency a b) t + deriv (gammaRatioFrequency c d) t) t :=
  ((hasDerivAt_gammaRatioFrequency ha hb t).differentiableAt.hasDerivAt.const_add v).add
    (hasDerivAt_gammaRatioFrequency hc hd t).differentiableAt.hasDerivAt

/-- Every genuine shifted two-Gamma phase satisfies a uniform square-root integral bound
on all subintervals of a sufficiently high dyadic block, for every linear modulation. -/
theorem norm_doubleGammaOscillatoryPhase_integral_le {a b c d T l r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hT : 128 ≤ T) (haT : a ≤ T) (hbT : b ≤ T) (hcT : c ≤ T) (hdT : d ≤ T)
    (hl : T ≤ l) (hlr : l ≤ r) (hr : r ≤ 2 * T) (v : ℝ) :
    ‖∫ t in l..r, doubleGammaOscillatoryPhase a b c d v t‖ ≤ 8 * Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  apply norm_phase_integral_le_sqrt_scale
    (fun t => (hasDerivAt_doubleGammaFrequency ha hb hc hd v t).differentiableAt)
    (hasDerivAt_doubleGammaOscillatoryPhase ha hb hc hd v)
    (norm_doubleGammaOscillatoryPhase ha hb hc hd v 0) hlr hT0
  intro t ht
  rw [(hasDerivAt_doubleGammaFrequency ha hb hc hd v t).deriv]
  have hTt := hl.trans ht.1
  have ht0 : 0 < t := hT0.trans_le hTt
  have h1 := (gammaRatioFrequency_deriv_bounds ha hb (hT.trans hTt)
    (haT.trans hTt) (hbT.trans hTt)).2
  have h2 := (gammaRatioFrequency_deriv_bounds hc hd (hT.trans hTt)
    (hcT.trans hTt) (hdT.trans hTt)).2
  have hrec := one_div_le_one_div_of_le ht0 (ht.2.trans hr)
  have he : 2 * (-1 / (2 * t)) = -(1 / t) := by ring
  linarith

end
end Dubon2026
