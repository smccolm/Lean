import Dubon2026.PhaseSecondDerivative

/-! # Uniform dyadic oscillation of the genuine critical-line Rankin Gamma phase -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- The actual two-Gamma reflected phase with the linear Mellin frequency factor. -/
def rankinOscillatoryPhase (k : ℤ) (v t : ℝ) : ℂ :=
  Complex.exp (I * ((v * t : ℝ) : ℂ)) * rankinGammaPhase k t

/-- The exact real frequency of the linearly modulated Gamma phase. -/
def rankinOscillatoryFrequency (k : ℤ) (v t : ℝ) : ℝ := v + rankinGammaFrequency k t

/-- The actual modulated phase has unit modulus everywhere at positive integral weight. -/
theorem norm_rankinOscillatoryPhase {k : ℤ} (hk : 0 < k) (v t : ℝ) :
    ‖rankinOscillatoryPhase k v t‖ = 1 := by
  simp [rankinOscillatoryPhase, Complex.norm_exp, norm_rankinGammaPhase hk]

/-- The phase derivative uses its actual Mellin frequency and the genuine Gamma logarithmic derivatives. -/
theorem hasDerivAt_rankinOscillatoryPhase {k : ℤ} (hk : 0 < k) (v t : ℝ) :
    HasDerivAt (rankinOscillatoryPhase k v)
      (I * (rankinOscillatoryFrequency k v t : ℂ) * rankinOscillatoryPhase k v t) t := by
  have he := ((((hasDerivAt_id t).const_mul v).ofReal_comp).const_mul I).cexp
  convert he.mul (hasDerivAt_rankinGammaPhase hk t) using 1
  simp only [rankinOscillatoryPhase, rankinOscillatoryFrequency, ofReal_add, id_eq, mul_one]
  ring

/-- The actual linearly modulated frequency is differentiable on all real heights. -/
theorem differentiable_rankinOscillatoryFrequency {k : ℤ} (hk : 0 < k) (v : ℝ) :
    Differentiable ℝ (rankinOscillatoryFrequency k v) := fun t =>
  ((hasDerivAt_rankinGammaFrequency hk t).const_add v).differentiableAt

/-- The linear modulation leaves the actual frequency curvature unchanged. -/
theorem deriv_rankinOscillatoryFrequency {k : ℤ} (hk : 0 < k) (v t : ℝ) :
    deriv (rankinOscillatoryFrequency k v) t = deriv (rankinGammaFrequency k) t := by
  exact ((hasDerivAt_rankinGammaFrequency hk t).differentiableAt.hasDerivAt.const_add v).deriv

/-- Every subinterval of a sufficiently high dyadic block has a uniform square-root bound,
for every real linear modulation, proved from the actual Gamma phase curvature. -/
theorem norm_rankinOscillatoryPhase_integral_le {k : ℤ} (hk : 0 < k)
    {T a b : ℝ} (hT : 128 ≤ T) (hkT : (k : ℝ) - 1 / 2 ≤ T)
    (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T) (v : ℝ) :
    ‖∫ t in a..b, rankinOscillatoryPhase k v t‖ ≤ 8 * Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hcurv (t : ℝ) (ht : t ∈ Icc a b) :
      deriv (rankinOscillatoryFrequency k v) t ≤ -(1 / (2 * T)) := by
    rw [deriv_rankinOscillatoryFrequency hk]
    have ht0 : 0 < t := hT0.trans_le (ha.trans ht.1)
    have hbound := (rankinGammaFrequency_deriv_bounds hk
      (hT.trans (ha.trans ht.1)) (hkT.trans (ha.trans ht.1))).2
    have hrec := one_div_le_one_div_of_le ht0 (ht.2.trans hb)
    rw [neg_div] at hbound
    linarith
  exact norm_phase_integral_le_sqrt_scale
    (differentiable_rankinOscillatoryFrequency hk v) (hasDerivAt_rankinOscillatoryPhase hk v)
    (norm_rankinOscillatoryPhase hk v 0) hab hT0 hcurv

end
end Dubon2026
