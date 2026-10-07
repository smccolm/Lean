import Dubon2026.GammaRieszTail

/-! # The genuine symmetric improper Riesz Gamma kernel -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate

noncomputable section

/-- Reflection of the actual unequal-shift Gamma quotient is complex conjugation. -/
theorem reflectedGammaRatio_neg_eq_conj (a b t : ℝ) :
    reflectedGammaRatio a b (-t) = conj (reflectedGammaRatio a b t) := by
  simp [reflectedGammaRatio, gammaVerticalPoint_neg, Gamma_conj]

/-- The literal Riesz Gamma integrand has exact conjugate symmetry. -/
theorem gammaRieszIntegrand_neg_eq_conj {x : ℝ} (hx : 0 < x) (k r t : ℝ) :
    gammaRieszIntegrand k r x (-t) = conj (gammaRieszIntegrand k r x t) := by
  have he : Complex.exp (I * ((Real.log x * (-t) : ℝ) : ℂ)) =
      conj (Complex.exp (I * ((Real.log x * t : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [gammaRieszIntegrand_eq hx, gammaRieszIntegrand_eq hx, he,
    reflectedGammaRatio_neg_eq_conj, reflectedGammaRatio_neg_eq_conj]
  simp only [map_mul, Complex.conj_ofReal]

/-- Every finite symmetric cutoff is exactly the sum of the positive-half integral and its conjugate. -/
theorem gammaRiesz_symmetric_integral_eq {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) (u : ℝ) :
    (∫ t in -u..u, gammaRieszIntegrand k r x t) =
      (∫ t in 0..u, gammaRieszIntegrand k r x t) + conj (∫ t in 0..u, gammaRieszIntegrand k r x t) := by
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  have hneg : (∫ t in -u..0, gammaRieszIntegrand k r x t) =
      conj (∫ t in 0..u, gammaRieszIntegrand k r x t) := by
    have he := intervalIntegral.integral_comp_neg (f := gammaRieszIntegrand k r x) (a := 0) (b := u)
    simp only [neg_zero] at he
    rw [← he, intervalIntegral.integral_congr (fun t _ => gammaRieszIntegrand_neg_eq_conj hx k r t)]
    simp only [intervalIntegral, integral_conj, map_sub]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-u) 0)
    (hc.intervalIntegrable 0 u), hneg, add_comm]

/-- The genuine positive-half integral is defined by its actual finite-cutoff limit. -/
def gammaRieszPositiveIntegral (k r x : ℝ) : ℂ :=
  limUnder atTop (fun u : ℝ => ∫ t in 0..u, gammaRieszIntegrand k r x t)

/-- The positive-half finite integrals converge to the defined actual limit. -/
theorem tendsto_gammaRieszPositiveIntegral {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    Tendsto (fun u : ℝ => ∫ t in 0..u, gammaRieszIntegrand k r x t) atTop
      (𝓝 (gammaRieszPositiveIntegral k r x)) :=
  tendsto_nhds_limUnder (exists_tendsto_gammaRieszIntegral hk hr0 hr2 hx)

/-- The Riesz Gamma kernel, with the exact inverse-Mellin normalization, is a symmetric improper limit. -/
def gammaRieszKernel (k r x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • (gammaRieszPositiveIntegral k r x + conj (gammaRieszPositiveIntegral k r x))

/-- The kernel is the limit of the literal normalized symmetric finite Gamma integrals. -/
theorem tendsto_gammaRieszKernel {k r x : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x) :
    Tendsto (fun u : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t in -u..u, gammaRieszIntegrand k r x t)
      atTop (𝓝 (gammaRieszKernel k r x)) := by
  have ht := tendsto_gammaRieszPositiveIntegral hk hr0 hr2 hx
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp ht
  simpa only [gammaRiesz_symmetric_integral_eq hk hr0 hr2 hx, gammaRieszKernel] using
    (ht.add hc).const_smul (1 / (2 * Real.pi) : ℝ)

/-- Conjugate symmetry makes the actual normalized improper kernel real. -/
theorem gammaRieszKernel_im (k r x : ℝ) : (gammaRieszKernel k r x).im = 0 := by
  simp [gammaRieszKernel, Complex.real_smul]

end
end Dubon2026
