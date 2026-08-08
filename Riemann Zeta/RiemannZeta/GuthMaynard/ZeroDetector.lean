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


/-- One past the natural-number floor of the detector's divisor cutoff. -/
noncomputable def detectorCutoff (T : ℝ) : ℕ :=
  ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ + 1

/-- The exact finite support of the truncated Möbius sum in the divisor variable. -/
noncomputable def detectorDivisors (n : ℕ) (T : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ))

@[simp]
lemma mem_detectorDivisors {d n : ℕ} {T : ℝ} :
    d ∈ detectorDivisors n T ↔
      (d ∣ n ∧ n ≠ 0) ∧ (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
  simp [detectorDivisors, Nat.mem_divisors]

/-- Every retained divisor lies below the natural cutoff, uniformly in `n`. -/
lemma detectorDivisors_subset_range (n : ℕ) (T : ℝ) :
    detectorDivisors n T ⊆ Finset.range (detectorCutoff T) := by
  intro d hd
  rw [mem_detectorDivisors] at hd
  rw [Finset.mem_range, detectorCutoff]
  have hdlt : (d : ℝ) < (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) + 1 :=
    hd.2.trans_lt (Nat.lt_floor_add_one (2 * T ^ (1 / 100 : ℝ)))
  exact_mod_cast hdlt

lemma detectorDivisors_card_le_cutoff (n : ℕ) (T : ℝ) :
    (detectorDivisors n T).card ≤ detectorCutoff T := by
  simpa using Finset.card_le_card (detectorDivisors_subset_range n T)

/- Actual truncated Möbius divisor sum
   `∑_{d ∣ n, d ≤ 2 T^(1/100)} μ(d)`. -/
noncomputable def mobius_sum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ d ∈ detectorDivisors n T, (ArithmeticFunction.moebius d : ℂ)

noncomputable def detectorCoeff (n : ℕ) (T : ℝ) : ℂ :=
  (mobius_sum n T) * Real.exp (-(n : ℝ) / (T ^ (1/2 : ℝ)))

/-- Magnitude property for the detector coefficient. Its quantifier order permits
    the constant to depend on `T`, while remaining uniform in positive `n`. -/
def DetectorCoeffBoundProp : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (T : ℝ), 1 ≤ T → 
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ‖detectorCoeff n T‖ ≤ C * (n : ℝ) ^ ε

lemma norm_moebius_cast_le_one (d : ℕ) :
    ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- Truncation bounds the Möbius sum by a quantity depending only on `T`. -/
lemma norm_mobius_sum_le_cutoff (n : ℕ) (T : ℝ) :
    ‖mobius_sum n T‖ ≤ (detectorCutoff T : ℝ) := by
  calc
    ‖mobius_sum n T‖
        ≤ ∑ d ∈ detectorDivisors n T,
            ‖(ArithmeticFunction.moebius d : ℂ)‖ := by
          simpa [mobius_sum] using
            norm_sum_le (detectorDivisors n T)
              (fun d => (ArithmeticFunction.moebius d : ℂ))
    _ ≤ ∑ _d ∈ detectorDivisors n T, (1 : ℝ) := by
      exact Finset.sum_le_sum fun d _ => norm_moebius_cast_le_one d
    _ = ((detectorDivisors n T).card : ℝ) := by simp
    _ ≤ (detectorCutoff T : ℝ) := by
      exact_mod_cast detectorDivisors_card_le_cutoff n T

@[simp]
lemma detectorCoeff_eq_zero_iff (n : ℕ) (T : ℝ) :
    detectorCoeff n T = 0 ↔ mobius_sum n T = 0 := by
  rw [detectorCoeff, mul_eq_zero]
  simp

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

/-- The smoothed detector coefficient has the same uniform-in-`n` cutoff bound. -/
lemma norm_detectorCoeff_le_cutoff (n : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ‖detectorCoeff n T‖ ≤ (detectorCutoff T : ℝ) := by
  rw [detectorCoeff, norm_mul]
  calc
    ‖mobius_sum n T‖ *
          ‖(Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)‖
        ≤ (detectorCutoff T : ℝ) * 1 := by
          apply mul_le_mul (norm_mobius_sum_le_cutoff n T)
          · rw [Complex.norm_real]
            exact exp_smoothing_bound n T hT
          · positivity
          · positivity
    _ = (detectorCutoff T : ℝ) := mul_one _

/-- F-02: The actual truncated detector coefficients satisfy the stated
    epsilon-power magnitude bound, uniformly in `n` for each fixed `T`. -/
theorem detectorCoeff_bound : DetectorCoeffBoundProp := by
  intro ε hε T hT
  refine ⟨(detectorCutoff T : ℝ) + 1, by positivity, ?_⟩
  intro n hn
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn_one hε.le
  calc
    ‖detectorCoeff n T‖ ≤ (detectorCutoff T : ℝ) :=
      norm_detectorCoeff_le_cutoff n T hT
    _ ≤ ((detectorCutoff T : ℝ) + 1) * 1 := by norm_num
    _ ≤ ((detectorCutoff T : ℝ) + 1) * (n : ℝ) ^ ε := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

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
