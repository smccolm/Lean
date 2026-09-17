import Tao2026.SpecializedIntervalReduction
import Tao2026.FourierRadial

/-!
# Quantitative specialized Fourier reconstruction

This module records the exact outer-coefficient-tail cost for passing from a
finite Fourier box to a smooth periodic weight in the specialized `M = N`,
`j = 2` discrepancy.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace Tao2026

noncomputable section

/-- A square Fourier truncation transfers to the original periodic weight at
the exact outer-box coefficient-tail cost. -/
theorem norm_specializedSmoothDiscrepancy_le_coefficientTail
    {P : ℕ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (W : ℝ × ℝ → ℂ) (hWcont : Continuous W)
    (hper : IsZ2Periodic W) {C : ℝ}
    (hc : ∀ q, ‖taoFourierCoeff W hper hWcont q‖ ≤
      C * fourierDecayWeight q)
    (R : ℕ) (N : ℝ) {E : ℝ}
    (hPolynomialError :
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R)
              (taoFourierCoeff W hper hWcont)) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R)
              (taoFourierCoeff W hper hWcont)) N N 2‖ ≤ E) :
    let δ := ∑' q : {q // q ∉ fourierFrequencyBox R},
      ‖taoFourierCoeff W hper hWcont q‖
    ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
        primeEquidistributionIntegral I W N N 2‖ ≤
      (2 * (P : ℝ) + 1) * δ + E + (δ / Real.log P) * P := by
  dsimp only
  apply norm_primeEquidistributionDiscrepancy_le_of_finiteFourierApprox
    (by exact_mod_cast hP) hImeas hI W hWcont
      (fourierFrequencyBox R) (taoFourierCoeff W hper hWcont) N N 2
      (tsum_nonneg fun _ => norm_nonneg _) _ hPolynomialError
  intro x
  exact norm_taoFourierPolynomial_sub_le_coefficientTail
    hper hWcont hc R x

/-- Smoothness replaces the literal coefficient tail by the radial cubic
decay tail times Tao's `C³` norm. -/
theorem norm_specializedSmoothDiscrepancy_le_decayTail
    {P : ℕ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (R : ℕ) (N : ℝ) {E : ℝ}
    (hPolynomialError :
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R)
              (taoFourierCoeff W hper hW.continuous)) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R)
              (taoFourierCoeff W hper hW.continuous)) N N 2‖ ≤ E) :
    let Δ := 27 * taoC3Norm W *
      (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q)
    ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
        primeEquidistributionIntegral I W N N 2‖ ≤
      (2 * (P : ℝ) + 1) * Δ + E + (Δ / Real.log P) * P := by
  have hraw := norm_specializedSmoothDiscrepancy_le_coefficientTail
    hP hImeas hI W hW.continuous hper
      (norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
        W hW hper)
    R N hPolynomialError
  have htail := taoFourierCoefficientTail_le_taoC3Norm_mul_decayTail
    W hW hper R
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  dsimp only at hraw ⊢
  refine hraw.trans ?_
  gcongr

/-- Conditional finite-box estimates on arbitrary real intervals transfer to
the original periodic weight with the exact coefficient-tail remainder. -/
theorem eventually_specializedSmoothDiscrepancy_le_coefficientTail_add_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (R : ℕ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    let δ := ∑' q : {q // q ∉ fourierFrequencyBox R},
      ‖taoFourierCoeff W hper hW.continuous q‖
    ∀ᶠ P : ℕ in atTop, ∀ (I : Set ℝ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        (2 * (P : ℝ) + 1) * δ +
          (P : ℝ) / (Real.log P) ^ S + (δ / Real.log P) * P := by
  dsimp only
  have hpoly :=
    eventually_specializedFiniteFourierPolynomial_interval_le_logSaving
      hPNT hVinogradov R (taoFourierCoeff W hper hW.continuous)
        hK hε haexp S
  filter_upwards [hpoly, eventually_ge_atTop (2 : ℕ)] with P hpolyP hP
  intro I N hImeas hconn hI hN
  exact norm_specializedSmoothDiscrepancy_le_coefficientTail hP hImeas hI
    W hW.continuous hper
      (norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth
        W hW hper)
    R N (hpolyP I N hImeas hconn hI hN)

/-- `C³`-normalized form of the preceding reconstruction bound.  The only
remaining truncation term is the universal radial envelope tail. -/
theorem eventually_specializedSmoothDiscrepancy_le_decayTail_add_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (W : ℝ × ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hper : IsZ2Periodic W) (R : ℕ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    let Δ := 27 * taoC3Norm W *
      (∑' q : {q // q ∉ fourierFrequencyBox R}, fourierDecayWeight q)
    ∀ᶠ P : ℕ in atTop, ∀ (I : Set ℝ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I W N N 2 -
          primeEquidistributionIntegral I W N N 2‖ ≤
        (2 * (P : ℝ) + 1) * Δ +
          (P : ℝ) / (Real.log P) ^ S + (Δ / Real.log P) * P := by
  dsimp only
  have hpoly :=
    eventually_specializedFiniteFourierPolynomial_interval_le_logSaving
      hPNT hVinogradov R (taoFourierCoeff W hper hW.continuous)
        hK hε haexp S
  filter_upwards [hpoly, eventually_ge_atTop (2 : ℕ)] with P hpolyP hP
  intro I N hImeas hconn hI hN
  exact norm_specializedSmoothDiscrepancy_le_decayTail hP hImeas hI
    W hW hper R N (hpolyP I N hImeas hconn hI hN)

end

end Tao2026
