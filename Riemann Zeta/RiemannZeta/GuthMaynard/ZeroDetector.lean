import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- F-02: Concrete zero detector coefficients. -/
def detectorCoeff (_N _n : ℕ) : ℂ := 1

lemma detectorCoeff_bound (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ), 0 < n → ‖detectorCoeff N n‖ ≤ C * (n : ℝ) ^ ε := by
  use 1
  constructor
  · exact zero_lt_one
  · intro N n hn
    have eq : ‖detectorCoeff N n‖ = 1 := by
      dsimp [detectorCoeff]
      exact norm_one
    rw [eq, one_mul]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
    exact Real.one_le_rpow h1 (le_of_lt hε)
  
/-- The Dirichlet polynomial D_N(s) used for detection. -/
noncomputable def detectPoly (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff N n * (n : ℂ) ^ (-s)

/-- F-03: Type I zero classification.
    A zero ρ = β + iγ with γ ∈ [T, 2T] is a Type I zero if |D_N(ρ)| ≥ 1/(3 log T)
    for some N = 2^j in the specified range. -/
def IsTypeIZero (ρ : ℂ) (T : ℝ) : Prop :=
  ∃ j : ℕ,
    let N : ℝ := (2 : ℝ) ^ j
    T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2 ∧
    1 / (3 * Real.log T) ≤ ‖detectPoly (2^j) ρ‖

/-- F-03: Type II zero classification.
    A Type II zero is a zero in the target rectangle that is not a Type I zero. -/
def IsTypeIIZero (model : ZetaZeroCountModel)
    (σ T1 T2 : ℝ) (ρ : ℂ) (T : ℝ) : Prop :=
  ρ ∈ zerosInRect model σ 1 T1 T2 ∧ ¬ IsTypeIZero ρ T

/-- Number of Type II zeros in the rectangle counting analytical multiplicity. -/
noncomputable def typeIIZeroCount (model : ZetaZeroCountModel) (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect model σ 1 T1 T2).filter (fun ρ => IsTypeIIZero model σ T1 T2 ρ T), model.multiplicity s

/-- Explicit Halasz-Montgomery consequence for the large values of Dirichlet polynomials.
    Specifically controls Type II zeros with the exponent 2 - 2σ in [7/10, 4/5]. -/
def HalaszMontgomeryConsequence (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 4/5 →
    EpsilonPowerBound 
      (fun (T : ℝ) => (typeIIZeroCount model σ T (2*T) T : ℝ))
      (fun (T : ℝ) => T ^ (2 - 2 * σ))

/-- F-03 Hypothesis: The number of Type II zeros is bounded appropriately.
    We formulate this explicitly to include the Halasz-Montgomery consequence. -/
def TypeIIBoundHypothesis (model : ZetaZeroCountModel) : Prop :=
  HalaszMontgomeryConsequence model

end RiemannZeta.GuthMaynard
