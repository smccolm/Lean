import Dubon2026.GammaRieszJointContinuity
import Dubon2026.CompactParameterDerivative

/-! # Differentiation under the actual finite Riesz Gamma integral -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A weighted actual cutoff is exactly the integral of the genuine weighted integrand. -/
theorem gammaRieszWeightedCutoff_eq (k r c x T : ℝ) :
    ((x ^ r : ℝ) : ℂ) * gammaRieszVerticalCutoff k r (c * x) (3 / 8) T =
      (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T,
        gammaRieszWeightedIntegrand k r c (3 / 8) t x := by
  simp only [gammaRieszWeightedIntegrand, gammaRieszVerticalCutoff,
    intervalIntegral.integral_const_mul, Complex.real_smul]
  ring

/-- Compact joint continuity supplies domination for differentiating the actual finite cutoff. -/
theorem hasDerivAt_gammaRieszWeightedCutoff {k r c x : ℝ} (hk : 2 ≤ k)
    (hr : 1 ≤ r) (hc : 0 < c) (hx : 0 < x) (T : ℝ) :
    HasDerivAt (fun y : ℝ => ((y ^ r : ℝ) : ℂ) *
        gammaRieszVerticalCutoff k r (c * y) (3 / 8) T)
      (((x ^ (r - 1) : ℝ) : ℂ) * gammaRieszVerticalCutoff k (r - 1) (c * x) (3 / 8) T) x := by
  have hh := hasDerivAt_intervalIntegral_of_positive_compact_joint
    (F := fun y t => gammaRieszWeightedIntegrand k r c (3 / 8) t y)
    (F' := fun y t => gammaRieszWeightedIntegrand k (r - 1) c (3 / 8) t y)
    hx (-T) T (fun y hy => continuous_gammaRieszWeightedIntegrand_height hk (by linarith) hc hy)
    (fun t _ => continuousAt_gammaRieszWeightedIntegrand_joint hk (by linarith) hc hx t)
    (fun y hy t _ => hasDerivAt_gammaRieszWeightedIntegrand hr hc hy k t)
  have hh' := hh.const_smul (1 / (2 * Real.pi) : ℝ)
  change HasDerivAt (fun y => (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T,
    gammaRieszWeightedIntegrand k r c (3 / 8) t y) _ x at hh'
  simpa only [← gammaRieszWeightedCutoff_eq] using hh'

end
end Dubon2026
