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
  /-- The coefficient magnitude bound. -/
  coeff_bound : ∀ N n, ‖coeff N n‖ ≤ 1 -- Simplification for the analytic interface
  
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

/-- F-03 Hypothesis: The number of Type II zeros is bounded by T^{2-2σ} (log T)^{O(1)}.
    Formulated using the T^{o(1)} epsilon-power convention. -/
def TypeIIBoundHypothesis (model : ZetaZeroCountModel) (detector : ZeroDetectorModel) : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 1 →
    EpsilonPowerBound 
      (fun (T : ℝ) => (((zerosInRect model σ 1 T (2*T)).filter 
        (fun ρ => IsTypeIIZero model detector σ T (2*T) ρ T)).card : ℝ))
      (fun (T : ℝ) => T ^ (2 - 2 * σ))

end RiemannZeta.GuthMaynard
