import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Complex MeasureTheory Filter Topology

namespace RiemannZeta.GuthMaynard

noncomputable def fourierTransformΦ (Φ : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ (x : ℝ), (Φ x : ℂ) * cexp (-(2 * Real.pi * I * x * ξ))

def FourierInversionProp (Φ : ℝ → ℝ) : Prop :=
  ∀ (x : ℝ), (Φ x : ℂ) = ∫ (ξ : ℝ), fourierTransformΦ Φ ξ * cexp (2 * Real.pi * I * x * ξ)

theorem fourier_inversion_native (Φ : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ Φ) (h_compact : HasCompactSupport Φ) : FourierInversionProp Φ := by
  sorry

end RiemannZeta.GuthMaynard
