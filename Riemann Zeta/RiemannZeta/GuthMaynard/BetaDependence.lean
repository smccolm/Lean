import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.ZeroCount
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral

open Complex
open MeasureTheory

namespace RiemannZeta.GuthMaynard

-- 1. Smooth Cutoff Function and its Fourier Transform
variable (Φ : ℝ → ℝ)
variable (Φ_smooth : ContDiff ℝ ⊤ Φ)
variable (Φ_compact : HasCompactSupport Φ)

-- The Fourier transform of Φ
noncomputable def fourierTransformΦ (Φ : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ (x : ℝ), (Φ x : ℂ) * cexp (-(2 * Real.pi * I * x * ξ))

-- 2. Fourier Inversion Formula (Hypothesis)
/--
Hypothesis: Fourier inversion holds for our smooth cutoff function.
-/
def FourierInversionHypothesis (Φ : ℝ → ℝ) : Prop :=
  ∀ (x : ℝ), (Φ x : ℂ) = ∫ (ξ : ℝ), fourierTransformΦ Φ ξ * cexp (2 * Real.pi * I * x * ξ)

-- 3. Rapid Decay of the Fourier Transform (Hypothesis)
/--
Hypothesis: The Fourier transform of a smooth compactly supported function has rapid decay.
For any integer N > 0, there is a constant C_N such that |F(Φ)(ξ)| ≤ C_N * (1 + |ξ|)^{-N}.
-/
def FourierDecayHypothesis (Φ : ℝ → ℝ) : Prop :=
  ∀ (N : ℕ), ∃ C : ℝ, ∀ ξ : ℝ, ‖fourierTransformΦ Φ ξ‖ ≤ C * (1 + |ξ|) ^ (- (N : ℝ))

-- We introduce a predicate for P:
def IsDetectorFixedLinePolynomial (Φ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (P : ℂ → ℂ) : Prop :=
  ∀ (β γ : ℝ),
    detectPoly N (β + I * γ) = ∫ (v : ℝ), fourierTransformΦ Φ v * P (σ + I * (γ + v))

-- 4. Integral representation over fixed line Re(s) = σ (Hypothesis)
/--
Hypothesis: A detector polynomial D(β + iγ) can be expressed as an integral over the fixed line Re(s) = σ
using the Fourier transform to extract a shift.
-/
def DetectorFixedLineIntegralHypothesis (Φ : ℝ → ℝ) : Prop :=
  ∀ (N : ℕ) (σ : ℝ), ∃ (P : ℂ → ℂ), IsDetectorFixedLinePolynomial Φ N σ P

-- 5. Coefficient bounds and epsilon losses (Hypothesis)
/--
Hypothesis: The polynomial P on the fixed line preserves coefficient bounds up to epsilon losses.
-/
def FixedLineCoefficientBoundsHypothesis (Φ : ℝ → ℝ) : Prop :=
  ∀ (T : ℝ) (σ : ℝ) (N : ℕ), T ≥ 1 → 
    ∀ (P : ℂ → ℂ), IsDetectorFixedLinePolynomial Φ N σ P →
      ∀ (β γ : ℝ),
        (1 / (3 * Real.log T) ≤ ‖detectPoly N (β + I * γ)‖) →
        ∃ (v : ℝ), |v| ≤ 1 ∧ 1 / (4 * Real.log T) ≤ ‖P (σ + I * (γ + v))‖

-- The final BetaDependenceRemovalHypothesis now assembled from these pieces.
/--
F-04: Beta dependence removal hypothesis.
For every T ≥ 1 and σ, there exists a polynomial P(s) such that if the detector D_N(s)
is large at a zero ρ = β + iγ, then P(σ + iγ') is large for some nearby γ'.
We explicitly parameterize this by the required analytic hypotheses.
-/
def BetaDependenceRemovalHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (Φ : ℝ → ℝ),
    FourierInversionHypothesis Φ →
    FourierDecayHypothesis Φ →
    DetectorFixedLineIntegralHypothesis Φ →
    FixedLineCoefficientBoundsHypothesis Φ →
    ∀ (T : ℝ) (σ : ℝ) (N : ℕ), T ≥ 1 → 
      ∃ (P : ℂ → ℂ), ∀ (ρ : ℂ), ρ ∈ zerosInRect model σ 1 T (2 * T) →
        1 / (3 * Real.log T) ≤ ‖detectPoly N ρ‖ →
        ∃ (γ' : ℝ), |ρ.im - γ'| ≤ 1 ∧ 1 / (4 * Real.log T) ≤ ‖P (σ + I * γ')‖

theorem beta_dependence_removal (model : ZetaZeroCountModel) : BetaDependenceRemovalHypothesis model := by
  intro Φ hInv hDecay hDet hBounds T σ N hT
  rcases hDet N σ with ⟨P, hP⟩
  use P
  intro ρ _ hLarge
  have h_eq : (ρ.re : ℂ) + I * (ρ.im : ℂ) = ρ := by
    rw [mul_comm]
    exact Complex.re_add_im ρ
  have hLarge' : 1 / (3 * Real.log T) ≤ ‖detectPoly N ((ρ.re : ℂ) + I * (ρ.im : ℂ))‖ := by
    rwa [h_eq]
  rcases hBounds T σ N hT P hP ρ.re ρ.im hLarge' with ⟨v, hv1, hv2⟩
  use ρ.im + v
  constructor
  · have eq1 : ρ.im - (ρ.im + v) = -v := by ring
    rw [eq1, abs_neg]
    exact hv1
  · push_cast
    exact hv2

end RiemannZeta.GuthMaynard
