import TaoTrudgianYang2025.BetaQuadraticParts

/-!
# Exact weighted quadratic Taylor decomposition

The odd first-order term integrates to zero. The remaining coefficient is
the actual integral of the second derivative, with its derivative controlled
by the original third derivative.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def quadraticTaylorCoefficient (W : ℝ → ℝ) : ℝ → ℝ :=
  segmentTaylorAverage (deriv (deriv W)) 0 0

theorem quadraticTaylorCoefficient_contDiff {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (quadraticTaylorCoefficient W) := by
  have hW₂ : ContDiff ℝ ∞ (deriv (deriv W)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (u := x) hW.contDiffAt 2
  exact segmentTaylorAverage_contDiff_global hW₂ 0 0

theorem quadraticTaylorCoefficient_deriv {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (z : ℝ) :
    deriv (quadraticTaylorCoefficient W) z = segmentTaylorAverage (deriv (deriv W)) 0 1 z := by
  have hW₂ : ContDiff ℝ ∞ (deriv (deriv W)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (u := x) hW.contDiffAt 2
  exact (segmentTaylorAverage_hasDerivAt_global hW₂ 0 z 0).deriv

theorem abs_quadraticTaylorCoefficient_le {W : ℝ → ℝ} {M : ℝ}
    (hb : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M) (z : ℝ) :
    |quadraticTaylorCoefficient W z| ≤ M := by
  apply abs_segmentTaylorAverage_le_global 0 z 0
  intro u
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb u

theorem abs_deriv_quadraticTaylorCoefficient_le {W : ℝ → ℝ} {M : ℝ}
    (hW : ContDiff ℝ ∞ W) (hb : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M) (z : ℝ) :
    |deriv (quadraticTaylorCoefficient W) z| ≤ M := by
  rw [quadraticTaylorCoefficient_deriv hW]
  apply abs_segmentTaylorAverage_le_global 0 z 1
  intro u
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb u

theorem integral_weighted_betaQuadraticKernel_taylor
    {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (T H : ℝ) :
    (∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z) =
      (W 0 : ℂ)*(∫ z in (-H)..H, betaQuadraticKernel T z)+
      ∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
        betaQuadraticKernel T z := by
  have hV := (quadraticTaylorCoefficient_contDiff hW).continuous
  have hK := continuous_betaQuadraticKernel T
  have hlinear : Continuous (fun z : ℝ => (z : ℂ)*betaQuadraticKernel T z) :=
    Complex.continuous_ofReal.mul hK
  have hquad : Continuous (fun z : ℝ => ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
      betaQuadraticKernel T z) :=
    (Complex.continuous_ofReal.comp ((continuous_id.pow 2).mul hV)).mul hK
  have he : (fun z : ℝ => (W z : ℂ)*betaQuadraticKernel T z) =
      (fun z : ℝ => (W 0 : ℂ)*betaQuadraticKernel T z+
        ((deriv W (0 : ℝ) : ℝ) : ℂ)*((z : ℂ)*betaQuadraticKernel T z)+
        ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*betaQuadraticKernel T z) := by
    funext z
    have h := segmentTaylorAverage_second_global hW 0 z
    simp only [sub_zero] at h
    have hw : W z = W 0+z*deriv W 0+z^2*quadraticTaylorCoefficient W z := by
      dsimp [quadraticTaylorCoefficient]
      linarith
    rw [hw]
    push_cast
    ring
  rw [he,intervalIntegral.integral_add
    (((hK.const_mul (W 0 : ℂ)).intervalIntegrable (-H) H).add
      ((hlinear.const_mul ((deriv W (0 : ℝ) : ℝ) : ℂ)).intervalIntegrable (-H) H))
    (hquad.intervalIntegrable (-H) H),
    intervalIntegral.integral_add
      ((hK.const_mul (W 0 : ℂ)).intervalIntegrable (-H) H)
      ((hlinear.const_mul ((deriv W (0 : ℝ) : ℝ) : ℂ)).intervalIntegrable (-H) H),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_betaQuadraticKernel_odd,mul_zero,add_zero]

end TaoTrudgianYang2025
