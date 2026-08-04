import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- F-02: Zero detector coefficients interface.
    Formalizes the existence of the weighted Dirichlet polynomial used in Section 13.1,
    without immediately proving its Mobius-inversion construction. -/
structure ZeroDetectorModel where
  /-- The coefficients of the zero detecting polynomial for a given N. -/
  coeff : ℕ → ℕ → ℂ
  /-- The coefficient magnitude bound by an epsilon power (since it involves a truncated divisor sum). -/
  coeff_bound : ∀ (ε : ℝ), 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ), 0 < n → ‖coeff N n‖ ≤ C * (n : ℝ) ^ ε
  
/-- The Dirichlet polynomial D_N(s) used for detection. -/
noncomputable def detectPoly (detector : ZeroDetectorModel) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), detector.coeff N n * (n : ℂ) ^ (-s)

/-- F-03: Type I zero classification.
    A zero ρ = β + iγ with γ ∈ [T, 2T] is a Type I zero if |D_N(ρ)| ≥ 1/(3 log T)
    for some N = 2^j in the specified range. -/
def IsTypeIZero (detector : ZeroDetectorModel) (ρ : ℂ) (T : ℝ) : Prop :=
  ∃ j : ℕ,
    let N : ℝ := (2 : ℝ) ^ j
    T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2 ∧
    1 / (3 * Real.log T) ≤ ‖detectPoly detector (2^j) ρ‖

/-- F-03: Type II zero classification.
    A Type II zero is a zero in the target rectangle that is not a Type I zero. -/
def IsTypeIIZero (model : ZetaZeroCountModel) (detector : ZeroDetectorModel)
    (σ T1 T2 : ℝ) (ρ : ℂ) (T : ℝ) : Prop :=
  ρ ∈ zerosInRect model σ 1 T1 T2 ∧ ¬ IsTypeIZero detector ρ T

/-- Explicit Halasz-Montgomery consequence for the large values of Dirichlet polynomials.
    Specifically controls Type II zeros with the exponent 3(1-σ)/(3σ-1) in [3/4, 4/5]. -/
def HalaszMontgomeryConsequence (model : ZetaZeroCountModel) (detector : ZeroDetectorModel) : Prop :=
  ∀ (σ : ℝ), 3/4 ≤ σ → σ ≤ 4/5 →
    EpsilonPowerBound 
      (fun (T : ℝ) => (((zerosInRect model σ 1 T (2*T)).filter 
        (fun ρ => IsTypeIIZero model detector σ T (2*T) ρ T)).card : ℝ))
      (fun (T : ℝ) => T ^ (3 * (1 - σ) / (3 * σ - 1)))

/-- F-03 Hypothesis: The number of Type II zeros is bounded appropriately.
    We formulate this explicitly to include the Halasz-Montgomery consequence. -/
def TypeIIBoundHypothesis (model : ZetaZeroCountModel) (detector : ZeroDetectorModel) : Prop :=
  HalaszMontgomeryConsequence model detector

end RiemannZeta.GuthMaynard
