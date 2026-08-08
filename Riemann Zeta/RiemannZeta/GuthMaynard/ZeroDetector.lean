import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors

open Complex
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard


/- Actual truncated Möbius divisor sum
   `∑_{d ∣ n, d ≤ 2 T^(1/100)} μ(d)`. -/
noncomputable def mobius_sum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun (d : ℕ) => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
    (ArithmeticFunction.moebius d : ℂ)

noncomputable def detectorCoeff (n : ℕ) (T : ℝ) : ℂ :=
  (mobius_sum n T) * Real.exp (-(n : ℝ) / (T ^ (1/2 : ℝ)))

/-- Hypothesis bounding the detector coefficient with epsilon losses. -/
def DetectorCoeffBoundProp : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (T : ℝ), 1 ≤ T → 
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ‖detectorCoeff n T‖ ≤ C * (n : ℝ) ^ ε

/-- Exponential decay bound for the smoothing factor -/
lemma exp_smoothing_bound (n : ℕ) (T : ℝ) (hT : 1 ≤ T) :
  ‖Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ))‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  have h_exp_pos : 0 ≤ Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ)) := (Real.exp_pos _).le
  rw [abs_of_nonneg h_exp_pos]
  have h1 : 0 ≤ T ^ (1/2 : ℝ) := by positivity
  have h2 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : 0 ≤ (n : ℝ) / T ^ (1/2 : ℝ) := div_nonneg h2 h1
  have h4 : -(n : ℝ) / T ^ (1/2 : ℝ) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr h3
  have h5 : Real.exp (-(n : ℝ) / T ^ (1/2 : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h4
  rw [Real.exp_zero] at h5
  exact h5

/-- The Dirichlet polynomial D_N(s) used for detection. Depends essentially on T. -/
noncomputable def detectPoly (N : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff n T * (n : ℂ) ^ (-s)

lemma detectPoly_eval (N : ℕ) (s : ℂ) (T : ℝ) :
  detectPoly N s T = ∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff n T * (n : ℂ) ^ (-s) := by
  rfl

/-- F-03: Type I zero classification.
    A zero ρ = β + iγ with γ ∈ [T, 2T] is a Type I zero if |D_N(ρ)| ≥ 1/(3 log T)
    for some N = 2^j in the specified range. -/
def IsTypeIZero (ρ : ℂ) (T : ℝ) : Prop :=
  ∃ j : ℕ,
    let N : ℝ := (2 : ℝ) ^ j
    T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2 ∧
    1 / (3 * Real.log T) ≤ ‖detectPoly (2^j) ρ T‖

/-- F-03: Type II zero classification.
    A Type II zero is a zero in the target rectangle that is not a Type I zero. -/
def IsTypeIIZero (σ T1 T2 : ℝ) (ρ : ℂ) (T : ℝ) : Prop :=
  ρ ∈ zerosInRect σ 1 T1 T2 ∧ ¬ IsTypeIZero ρ T

/-- Number of Type II zeros in the rectangle counting analytical multiplicity. -/
noncomputable def typeIIZeroCount (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => IsTypeIIZero σ T1 T2 ρ T), analyticVanishingOrder riemannZeta s

/-- Explicit Halasz-Montgomery consequence for the large values of Dirichlet polynomials.
    Specifically controls Type II zeros with the exponent 2 - 2σ throughout [7/10, 4/5]. 
    Replaces the Huxley estimate used earlier. -/
def HalaszMontgomeryConsequence : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 4/5 →
    EpsilonPowerBound 
      (fun (T : ℝ) => (typeIIZeroCount σ T (2*T) T : ℝ))
      (fun (T : ℝ) => T ^ (2 - 2 * σ))

lemma typeII_exponent_pos (σ : ℝ) (hσ2 : σ ≤ 4/5) :
  0 ≤ 2 - 2 * σ := by
  linarith

/-- F-03 Hypothesis: The number of Type II zeros is bounded appropriately. -/
def TypeIIBoundProp : Prop :=
  HalaszMontgomeryConsequence

end RiemannZeta.GuthMaynard
