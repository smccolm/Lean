import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
/-- The `mobius_sum` definition used by the source-facing construction in `ZeroDetector`. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def mobius_sum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ d ∈ detectorDivisors n T, (ArithmeticFunction.moebius d : ℂ)

/-- The `detectorCoeff` definition used by the source-facing construction in `ZeroDetector`. -/
noncomputable def detectorCoeff (n : ℕ) (T : ℝ) : ℂ :=
  (mobius_sum n T) * Real.exp (-(n : ℝ) / (T ^ (1/2 : ℝ)))

/-- Magnitude property for the detector coefficient. Its quantifier order permits
    the constant to depend on `T`, while remaining uniform in positive `n`. -/
def DetectorCoeffBoundProp : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (T : ℝ), 1 ≤ T → 
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ‖detectorCoeff n T‖ ≤ C * (n : ℝ) ^ ε

/-- The classical epsilon-power bound for the number of positive divisors.
    The constant may depend on `ε` but is uniform in positive `n`. -/
def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

/-- Source-uniform detector bound needed when the detector polynomial is powered.
    Unlike `DetectorCoeffBoundProp`, the constant is chosen before `T`. -/
def UniformDetectorCoeffBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (T : ℝ), 0 < n → 1 ≤ T →
      ‖detectorCoeff n T‖ ≤ C * (n : ℝ) ^ ε

/-- The truncated support is a subset of the full positive-divisor set. -/
lemma detectorDivisors_subset_divisors (n : ℕ) (T : ℝ) :
    detectorDivisors n T ⊆ n.divisors := by
  exact Finset.filter_subset _ _

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

/-- The truncated Möbius sum is bounded by the full divisor count, uniformly in `T`. -/
lemma norm_mobius_sum_le_divisors_card (n : ℕ) (T : ℝ) :
    ‖mobius_sum n T‖ ≤ (n.divisors.card : ℝ) := by
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
    _ ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (detectorDivisors_subset_divisors n T)

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

/-- The smoothed coefficient is bounded by the full divisor count, uniformly in `T`. -/
lemma norm_detectorCoeff_le_divisors_card (n : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    ‖detectorCoeff n T‖ ≤ (n.divisors.card : ℝ) := by
  rw [detectorCoeff, norm_mul]
  calc
    ‖mobius_sum n T‖ *
          ‖(Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)‖
        ≤ (n.divisors.card : ℝ) * 1 := by
          apply mul_le_mul (norm_mobius_sum_le_divisors_card n T)
          · rw [Complex.norm_real]
            exact exp_smoothing_bound n T hT
          · positivity
          · positivity
    _ = (n.divisors.card : ℝ) := mul_one _

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

/-- The exact detector satisfies the source-uniform epsilon-power estimate
    once the classical divisor-count bound is supplied. -/
theorem uniformDetectorCoeffBound_of_divisorCount
    (hDivisor : DivisorCountBoundProp) :
    UniformDetectorCoeffBoundProp := by
  intro ε hε
  obtain ⟨C, hC, hBound⟩ := hDivisor ε hε
  refine ⟨C, hC, ?_⟩
  intro n T hn hT
  exact (norm_detectorCoeff_le_divisors_card n T hT).trans (hBound n hn)

/-- The Dirichlet polynomial D_N(s) used for detection. Depends essentially on T. -/
noncomputable def detectPoly (N : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff n T * (n : ℂ) ^ (-s)

lemma detectPoly_eval (N : ℕ) (s : ℂ) (T : ℝ) :
  detectPoly N s T = ∑ n ∈ Finset.Ioc N (2 * N), detectorCoeff n T * (n : ℂ) ^ (-s) := by
  rfl

/-- The upper endpoint of the dyadic detector-scale range. -/
noncomputable def detectorScaleUpper (T : ℝ) : ℝ :=
  T ^ (1 / 2 : ℝ) * (Real.log T) ^ 2

/-- A dyadic exponent is admissible when its scale lies in the source range. -/
def IsAdmissibleDyadicScale (T : ℝ) (j : ℕ) : Prop :=
  T ^ (1 / 100 : ℝ) ≤ (2 : ℝ) ^ j ∧
    (2 : ℝ) ^ j ≤ detectorScaleUpper T

/-- A finite search bound for all admissible dyadic exponents. -/
noncomputable def dyadicScaleIndexCount (T : ℝ) : ℕ :=
  ⌊Real.logb 2 (detectorScaleUpper T)⌋₊ + 1

/-- The finite set of admissible dyadic detector exponents. -/
noncomputable def admissibleDyadicIndices (T : ℝ) : Finset ℕ :=
  (Finset.range (dyadicScaleIndexCount T)).filter (IsAdmissibleDyadicScale T)

lemma admissibleDyadicScale_index_lt (T : ℝ) (j : ℕ)
    (hj : IsAdmissibleDyadicScale T j) : j < dyadicScaleIndexCount T := by
  have hUpperPos : 0 < detectorScaleUpper T :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ j) hj.2
  have hjLog : (j : ℝ) ≤ Real.logb 2 (detectorScaleUpper T) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hUpperPos, Real.rpow_natCast]
    exact hj.2
  exact Nat.lt_succ_of_le (Nat.le_floor hjLog)

lemma mem_admissibleDyadicIndices (T : ℝ) (j : ℕ) :
    j ∈ admissibleDyadicIndices T ↔ IsAdmissibleDyadicScale T j := by
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (admissibleDyadicScale_index_lt T j hj), hj⟩

lemma admissibleDyadicIndices_card_le (T : ℝ) :
    (admissibleDyadicIndices T).card ≤ dyadicScaleIndexCount T := by
  unfold admissibleDyadicIndices
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

lemma detectorScaleUpper_le_rpow (T : ℝ) (hT : 1 ≤ T) :
    detectorScaleUpper T ≤ T ^ (5 / 2 : ℝ) := by
  have hT0 : 0 ≤ T := hT.trans' zero_le_one
  have hLog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hLogT : Real.log T ≤ T := Real.log_le_self hT0
  have hSq : (Real.log T) ^ 2 ≤ T ^ 2 := by nlinarith
  calc
    detectorScaleUpper T = T ^ (1 / 2 : ℝ) * (Real.log T) ^ 2 := rfl
    _ ≤ T ^ (1 / 2 : ℝ) * T ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hSq (Real.rpow_nonneg hT0 _)
    _ = T ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)]
      congr 1
      norm_num

/-- The admissible dyadic scale count has the required logarithmic growth. -/
lemma dyadicScaleIndexCount_le_log (T : ℝ) (hT : Real.exp 2 ≤ T) :
    (dyadicScaleIndexCount T : ℝ) ≤
      ((5 / 2 : ℝ) / Real.log 2 + 1 / 2) * Real.log T := by
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 2) hT
  have hTone : 1 ≤ T := by
    have : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le hT).le
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogT : 2 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hT
    simpa using this
  have hUpperPos : 0 < detectorScaleUpper T := by
    unfold detectorScaleUpper
    positivity
  have hUpper : detectorScaleUpper T ≤ T ^ (5 / 2 : ℝ) :=
    detectorScaleUpper_le_rpow T hTone
  have hLogbUpper :
      Real.logb 2 (detectorScaleUpper T) ≤ (5 / 2 : ℝ) * Real.logb 2 T := by
    calc
      Real.logb 2 (detectorScaleUpper T) ≤ Real.logb 2 (T ^ (5 / 2 : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) hUpperPos hUpper
      _ = (5 / 2 : ℝ) * Real.logb 2 T := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hTpos]
  have hLogbUpperNonneg : 0 ≤ Real.logb 2 (detectorScaleUpper T) := by
    have hSqrt : 1 ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow hTone (by norm_num)
    have hLogSq : 1 ≤ (Real.log T) ^ 2 := by nlinarith
    have hUpperOne : 1 ≤ detectorScaleUpper T := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ T ^ (1 / 2 : ℝ) * (Real.log T) ^ 2 :=
          mul_le_mul hSqrt hLogSq zero_le_one (zero_le_one.trans hSqrt)
        _ = detectorScaleUpper T := rfl
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hUpperOne) hLogTwo.le
  change ((⌊Real.logb 2 (detectorScaleUpper T)⌋₊ + 1 : ℕ) : ℝ) ≤ _
  push_cast
  calc
    (⌊Real.logb 2 (detectorScaleUpper T)⌋₊ : ℝ) + 1
        ≤ Real.logb 2 (detectorScaleUpper T) + 1 := by
          gcongr
          exact Nat.floor_le hLogbUpperNonneg
    _ ≤ (5 / 2 : ℝ) * Real.logb 2 T + 1 := by linarith
    _ = ((5 / 2 : ℝ) / Real.log 2) * Real.log T + 1 := by
      rw [Real.logb]
      field_simp
    _ ≤ ((5 / 2 : ℝ) / Real.log 2) * Real.log T +
          (1 / 2 : ℝ) * Real.log T := by linarith
    _ = ((5 / 2 : ℝ) / Real.log 2 + 1 / 2) * Real.log T := by ring

/-- Detection at one particular admissible dyadic scale. -/
def IsTypeIZeroAtScale (ρ : ℂ) (T : ℝ) (j : ℕ) : Prop :=
  j ∈ admissibleDyadicIndices T ∧
    1 / (3 * Real.log T) ≤ ‖detectPoly (2 ^ j) ρ T‖

/-- F-03: Type I zero classification.
    A zero ρ = β + iγ with γ ∈ [T, 2T] is a Type I zero if |D_N(ρ)| ≥ 1/(3 log T)
    for some N = 2^j in the specified range. -/
def IsTypeIZero (ρ : ℂ) (T : ℝ) : Prop :=
  ∃ j : ℕ, IsTypeIZeroAtScale ρ T j

/-- The residual zero class used in the Type-I/complement partition.
    This is not Maynard--Pratt's contour-integral Type II condition. -/
def IsResidualZero (σ T1 T2 : ℝ) (ρ : ℂ) (T : ℝ) : Prop :=
  ρ ∈ zerosInRect σ 1 T1 T2 ∧ ¬ IsTypeIZero ρ T

/-- Number of residual zeros in the rectangle, counted with analytic multiplicity. -/
noncomputable def residualZeroCount (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => IsResidualZero σ T1 T2 ρ T),
    analyticVanishingOrder riemannZeta s

/-- Target bound for residual zeros throughout `σ ∈ [7/10, 4/5]`.
    A source-faithful proof first embeds residual zeros into the genuine
    contour-integral Type II class. -/
def ResidualZeroBoundProp : Prop :=
  ∀ (σ : ℝ), 7/10 ≤ σ → σ ≤ 4/5 →
    EpsilonPowerBound 
      (fun (T : ℝ) => (residualZeroCount σ T (2*T) T : ℝ))
      (fun (T : ℝ) => T ^ (2 - 2 * σ))

lemma typeII_exponent_pos (σ : ℝ) (hσ2 : σ ≤ 4/5) :
  0 ≤ 2 - 2 * σ := by
  linarith

end RiemannZeta.GuthMaynard
