import GafniTao.HeathBrownOneSidedZetaSquareAFE

/-!
# Opening the one-sided AFE into the divisor Dirichlet series

On a right line the one-sided contour contains `zeta(s)^2`, hence the
ordinary divisor-count `L`-series.  Dividing by the central Gamma factor
turns the residue into the ordinary critical-line zeta square.  These exact
identities are the analytic entry to Ivić (6.27)--(6.28).
-/

open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators
  Interval LSeries.notation

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownOneSidedGammaNormalization (t : ℝ) : ℂ :=
  Complex.Gammaℝ (afeCriticalPoint t) ^ 2

theorem heathBrownOneSidedGammaNormalization_ne_zero (t : ℝ) :
    heathBrownOneSidedGammaNormalization t ≠ 0 := by
  unfold heathBrownOneSidedGammaNormalization
  apply pow_ne_zero
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  norm_num [afeCriticalPoint]

/-- The literal divisor-series integrand on the right line. -/
noncomputable def heathBrownOneSidedDivisorContourIntegrand
    (t c u : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s : ℂ := afeCriticalPoint t + w
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
    (s * (1 - s)) ^ 2 * Complex.Gammaℝ s ^ 2 *
    LSeries (fun n : ℕ => (n.divisors.card : ℂ)) s /
    heathBrownOneSidedPoleNormalization t / w

/-- The ordinary-zeta normalization of the right-line divisor integrand. -/
noncomputable def heathBrownOneSidedNormalizedDivisorIntegrand
    (t c u : ℝ) : ℂ :=
  heathBrownOneSidedDivisorContourIntegrand t c u /
    heathBrownOneSidedGammaNormalization t

theorem heathBrownOneSidedContourIntegrand_eq_divisorContour
    (t u : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    heathBrownOneSidedContourIntegrand t
        ((c : ℂ) + (u : ℂ) * I) =
      heathBrownOneSidedDivisorContourIntegrand t c u := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s : ℂ := afeCriticalPoint t + w
  have hsre : 1 < s.re := by
    simp [s, w, afeCriticalPoint]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hLambda := completedRiemannZeta_eq_zeta_mul_GammaR
    (show 0 < s.re from lt_trans zero_lt_one hsre)
  have hzeta := riemannZeta_sq_eq_divisorLSeries hsre
  unfold heathBrownOneSidedContourIntegrand
    heathBrownOneSidedContourNumerator
    heathBrownOneSidedDivisorContourIntegrand
  dsimp only
  change (Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w *
      completedXiNumerator s ^ 2 /
      heathBrownOneSidedPoleNormalization t) / w = _
  rw [completedXiNumerator_eq s hs0 hs1, hLambda]
  simp only [mul_pow]
  rw [hzeta]
  ring

/-- The central completed residue divided by its Gamma factor is the
ordinary zeta square. -/
theorem completedZetaSquare_div_heathBrownGammaNormalization
    (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 /
        heathBrownOneSidedGammaNormalization t =
      riemannZeta (afeCriticalPoint t) ^ 2 := by
  have hre : 0 < (afeCriticalPoint t).re := by
    norm_num [afeCriticalPoint]
  rw [completedRiemannZeta_eq_zeta_mul_GammaR hre]
  unfold heathBrownOneSidedGammaNormalization
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hre]

/-- Ordinary-zeta form of the infinite-height one-sided AFE. -/
theorem heathBrownOneSidedAFE_zeta_vertical_limit_native
    (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ =>
      (VIntegral' (heathBrownOneSidedContourIntegrand t) c (-H) H +
        VIntegral' (heathBrownOneSidedContourIntegrand (-t)) c (-H) H) /
          heathBrownOneSidedGammaNormalization t)
      atTop (𝓝 (riemannZeta (afeCriticalPoint t) ^ 2)) := by
  have hafe :=
    (heathBrownOneSidedAFE_vertical_limit_native t hc).div_const
      (heathBrownOneSidedGammaNormalization t)
  simpa [completedZetaSquare_div_heathBrownGammaNormalization] using hafe

/-- Each finite right contour is exactly the normalized divisor-series
integral. -/
theorem vIntegral_heathBrownOneSided_divisor_eq
    (t c H : ℝ) (hc : 1 / 2 < c) :
    VIntegral' (heathBrownOneSidedContourIntegrand t) c (-H) H /
        heathBrownOneSidedGammaNormalization t =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ u in -H..H,
          heathBrownOneSidedNormalizedDivisorIntegrand t c u := by
  have hraw :
      VIntegral' (heathBrownOneSidedContourIntegrand t) c (-H) H =
        (1 / (2 * Real.pi : ℂ)) *
          ∫ u in -H..H,
            heathBrownOneSidedDivisorContourIntegrand t c u := by
    unfold VIntegral' VIntegral
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_congr]
    · field_simp [Real.pi_ne_zero]
    · intro u _hu
      exact heathBrownOneSidedContourIntegrand_eq_divisorContour t u hc
  rw [hraw]
  unfold heathBrownOneSidedNormalizedDivisorIntegrand
  rw [intervalIntegral.integral_div]
  ring

/-- The two divisor-series right contours converge to the ordinary zeta
square.  The second denominator deliberately remains the Gamma factor at
`t`, exactly as produced by division of the one-sided residue identity. -/
theorem heathBrownOneSidedDivisorAFE_zeta_limit_native
    (t : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun H : ℝ =>
      (1 / (2 * Real.pi : ℂ)) *
        (∫ u in -H..H,
            heathBrownOneSidedNormalizedDivisorIntegrand t c u) +
      (VIntegral' (heathBrownOneSidedContourIntegrand (-t)) c (-H) H /
        heathBrownOneSidedGammaNormalization t))
      atTop (𝓝 (riemannZeta (afeCriticalPoint t) ^ 2)) := by
  have hafe := heathBrownOneSidedAFE_zeta_vertical_limit_native t
    (show 0 < c by linarith)
  apply hafe.congr'
  filter_upwards with H
  rw [add_div, vIntegral_heathBrownOneSided_divisor_eq t c H hc]


end

end GafniTao
