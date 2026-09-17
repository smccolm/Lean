import Tao2026.SmoothNumberSaddleTilt
import Tao2026.SmoothNumberSaddleCurvature

/-!
# Local-limit form of the critical smooth-number saddle theorem

This file identifies the precise remaining analytic statement behind the
critical saddle asymptotic.  The target is not left as a ratio of an opaque
count and a main term: it is exactly convergence to one of the explicit
tilted cutoff expectation multiplied by its Gaussian scale.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- The stated critical saddle asymptotic is equivalent to the local-limit
normalization of the explicit tilted cutoff factor. -/
theorem criticalSmoothSaddleAsymptotic_iff_tiltedLocalLimit :
    TaoCriticalSmoothSaddleAsymptoticConclusion ↔
      ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
        IsTaoCriticalSmoothRegime X y α →
          Tendsto (fun n =>
            smoothSaddleCutoffFactor (X n) (y n)
                (smoothSaddlePoint (X n) (y n)) *
              smoothSaddleGaussianScale (X n) (y n))
            atTop (𝓝 1) := by
  constructor
  · intro hasymptotic α X y hα hregime
    have hratio := hasymptotic α X y hα hregime
    apply hratio.congr'
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact psiNat_div_smoothSaddleMainTerm_eq_cutoffFactor_mul_gaussianScale
      hX hy
  · intro hlocal α X y hα hregime
    have hratio := hlocal α X y hα hregime
    apply hratio.congr'
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    exact (psiNat_div_smoothSaddleMainTerm_eq_cutoffFactor_mul_gaussianScale
      hX hy).symm

end

end Tao2026
