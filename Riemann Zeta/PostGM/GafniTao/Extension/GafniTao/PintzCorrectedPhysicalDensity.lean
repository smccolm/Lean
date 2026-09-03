import GafniTao.PintzPhysicalDensity
import GafniTao.PintzCorrectedGram

/-!
# Pintz density inequality with the corrected partial-zeta envelope

This is the source-facing finite zero-density consumer of the corrected Gram
bound.  Unlike the first physical assembly, the separation scale is a free
parameter and the long-cutoff contribution decays as its reciprocal.
-/

open Finset Metric
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The detected high-zero density inequality with an arbitrary physical
separation `G` and the corrected dyadic Gram envelope. -/
theorem pintz_corrected_physical_high_density
    {eta T lambda G : ℝ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hlambda : pintzMobiusLambdaThreshold ≤ lambda)
    (hLambdaHeight : 2 * lambda ≤ T)
    (hG : 3 ≤ G)
    (hError : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      pintzEquation46ErrorBound (1 - rho.re) rho.im lambda
        (pintzPhysicalZetaMajorant eta T)
        (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4)
    (hAbsorb :
      2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          pintzCorrectedPhysicalGramMajorant eta lambda T G ≤
        pintzDetectedLowerBound eta lambda T ^ 2) :
    ((∑ rho ∈ pintzHighZeroSet eta T lambda,
        zeroMultiplicity rho : ℕ) : ℝ) *
        pintzDetectedLowerBound eta lambda T ^ 2 ≤
      (pintzSelectionLoss (2 * lambda) G T : ℝ) *
        (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
            (harmonic (pintzMobiusCutoff lambda) : ℝ))) := by
  have hsigma : 0 ≤ 1 - eta := by linarith
  have hGPos : 0 < G := lt_of_lt_of_le (by norm_num) hG
  have hlambdaPos : 0 < lambda := by
    have hthreshold := pintzMobiusLambdaThreshold_ge_eight.trans hlambda
    linarith
  have hV : 0 < pintzDetectedLowerBound eta lambda T := by
    unfold pintzDetectedLowerBound
    have hTQuarter : (1 / 2 : ℝ) ≤ T := by
      have hT8 : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hT
      linarith
    have hZ := pintzPhysicalZetaMajorant_pos
      (eta := eta) (T := T) hTQuarter
    apply one_div_pos.mpr
    exact mul_pos (mul_pos (by norm_num) hlambdaPos)
      (mul_pos (div_pos hZ heta) (Real.exp_pos _))
  have hTQuarter : (1 / 4 : ℝ) ≤ T := by
    have hT8 : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hT
    linarith
  have hM : 0 ≤ pintzCorrectedPhysicalGramMajorant eta lambda T G :=
    pintzCorrectedPhysicalGramMajorant_nonneg hTQuarter hGPos
  have hDetected : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      ∃ u : ℝ, |rho.im - u| ≤ 2 * lambda ∧
        pintzDetectedLowerBound eta lambda T ≤
          ‖pintzDetectedPolynomialIcc (2 * eta)
            (pintzMobiusCutoff lambda) u‖ := by
    intro rho hrho
    have hrhoFull := (Finset.mem_filter.mp hrho).1
    have hheight := (Finset.mem_filter.mp hrho).2
    exact exists_large_pintzDetectedPolynomial_of_mem_zeroSet
      heta (by linarith) hlambda hheight hLambdaHeight hrhoFull
        (hError rho hrho)
  have hGram : ∀ t u : ℝ,
      |t| ≤ T + 2 * lambda → |u| ≤ T + 2 * lambda →
      G ≤ dist t u →
      ‖pintzGramCorrelation (2 * eta) (pintzMobiusCutoff lambda) t u‖ ≤
        pintzCorrectedPhysicalGramMajorant eta lambda T G := by
    intro t u ht hu hsep
    exact norm_pintzGramCorrelation_le_correctedPhysicalMajorant
      heta.le (by linarith) hG hsep ht hu hLambdaHeight
  have hfinite := pintz_finite_subset_density
    (pintzHighZeroSet eta T lambda)
    (pintzHighZeroSet_subset eta T lambda) hsigma hT hGPos
    (by positivity : 0 ≤ 2 * eta) hV hM hDetected hGram hAbsorb
  have hexponent : 2 * (2 * eta) = 4 * eta := by ring
  rw [hexponent] at hfinite
  exact hfinite

/-- Full finite Pintz inequality with the corrected long-cutoff Gram term. -/
theorem pintz_corrected_physical_finite_density
    {eta T lambda G : ℝ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hlambda : pintzMobiusLambdaThreshold ≤ lambda)
    (hLambdaHeight : 2 * lambda ≤ T)
    (hG : 3 ≤ G)
    (hError : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      pintzEquation46ErrorBound (1 - rho.re) rho.im lambda
        (pintzPhysicalZetaMajorant eta T)
        (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4)
    (hAbsorb :
      2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          pintzCorrectedPhysicalGramMajorant eta lambda T G ≤
        pintzDetectedLowerBound eta lambda T ^ 2) :
    (zeroCount (1 - eta) T : ℝ) *
        pintzDetectedLowerBound eta lambda T ^ 2 ≤
      (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 +
      (pintzSelectionLoss (2 * lambda) G T : ℝ) *
        (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
            (harmonic (pintzMobiusCutoff lambda) : ℝ))) := by
  have hlow := pintz_low_zero_weight_le
    (eta := eta) (T := T) (lambda := lambda) (by linarith) hT
  have hhigh := pintz_corrected_physical_high_density heta hetaUpper hT
    hlambda hLambdaHeight hG hError hAbsorb
  have hlowReal :
      ((∑ rho ∈ pintzLowZeroSet eta T lambda,
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℕ) := by
    exact_mod_cast hlow
  have hlowMul :
      ((∑ rho ∈ pintzLowZeroSet eta T lambda,
          zeroMultiplicity rho : ℕ) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 ≤
        ((2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℕ) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 :=
    mul_le_mul_of_nonneg_right hlowReal
      (sq_nonneg (pintzDetectedLowerBound eta lambda T))
  push_cast at hlowMul
  push_cast at hhigh
  rw [zeroCount_eq_pintz_high_add_low eta T lambda]
  push_cast
  calc
    (∑ x ∈ pintzHighZeroSet eta T lambda, (zeroMultiplicity x : ℝ) +
        ∑ x ∈ pintzLowZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 =
      (∑ x ∈ pintzHighZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 +
        (∑ x ∈ pintzLowZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 := by ring
    _ ≤ (pintzSelectionLoss (2 * lambda) G T : ℝ) *
          (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
            ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
              (harmonic (pintzMobiusCutoff lambda) : ℝ))) +
        (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 :=
      add_le_add hhigh hlowMul
    _ = _ := by ring

#print axioms pintz_corrected_physical_high_density
#print axioms pintz_corrected_physical_finite_density

end

end GafniTao
