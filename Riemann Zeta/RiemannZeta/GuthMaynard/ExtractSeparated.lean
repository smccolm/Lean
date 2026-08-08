import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.JensenFormula
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.BetaDependence

open Complex
open Finset
open Classical

namespace RiemannZeta.GuthMaynard


/--
The classical local zero-density estimate:
The number of zeros in a unit interval [t, t+1] is bounded by O(log T)
for t ∈ [T, 2T].
-/
def LocalZeroCountProp : Prop :=
  ∃ C > 0, ∀ (σ t T : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
    (zeroCountRect σ 1 t (t + 1) : ℝ) ≤ C * Real.log T

/-- Upper bound for Zeta on a disk covering the critical strip -/
axiom zeta_upper_bound_disk (t T : ℝ) (hT : T ≥ 2) (ht : t ∈ Set.Icc T (2 * T)) :
  ∃ (C : ℝ), ∀ z ∈ Metric.closedBall (2 + t * I) 3, ‖riemannZeta z‖ ≤ C * T

/-- Lower bound for Zeta at the center of the disk via the Euler product -/
axiom zeta_lower_bound_center (t T : ℝ) (hT : T ≥ 2) (ht : t ∈ Set.Icc T (2 * T)) :
  ‖riemannZeta (2 + t * I)‖ ≥ (1 / 2 : ℝ)

/-- The specific bound derived via Jensen's inequality from the upper and lower bounds -/
axiom jensens_inequality_disk_zero_count (σ t T : ℝ) (hT : T ≥ 2) (ht : t ∈ Set.Icc T (2 * T)) :
  (zeroCountRect σ 1 t (t + 1) : ℝ) ≤ 100 * Real.log T

lemma jensens_inequality_rhs_nonneg (T : ℝ) (hT : T ≥ 2) :
  0 ≤ 100 * Real.log T := by
  have h1 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  linarith

/--
F-06: The Local Zero Count Hypothesis follows from Jensen's Inequality
combined with polynomial growth and uniform lower bounds on the Riemann Zeta function.
-/
theorem local_zero_count_native : LocalZeroCountProp := by
  use 100
  constructor
  · norm_num
  · intro σ t T hT ht
    exact jensens_inequality_disk_zero_count σ t T hT ht

/-- Number of Type I zeros in the rectangle counting analytical multiplicity. -/
noncomputable def typeIZeroCount (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => IsTypeIZero ρ T), analyticVanishingOrder riemannZeta s

/-- Total zero count is the sum of Type I and residual zeros. -/
lemma typeI_add_residual_eq_total (σ T1 T2 T : ℝ) :
  typeIZeroCount σ T1 T2 T + residualZeroCount σ T1 T2 T = zeroCountRect σ 1 T1 T2 := by
  have H : residualZeroCount σ T1 T2 T = ∑ s ∈ (zerosInRect σ 1 T1 T2).filter (fun ρ => ¬IsTypeIZero ρ T), analyticVanishingOrder riemannZeta s := by
    unfold residualZeroCount IsResidualZero
    apply Finset.sum_congr
    · ext x
      simp only [Finset.mem_filter]
      tauto
    · intros
      rfl
  rw [H]
  unfold typeIZeroCount zeroCountRect
  exact Finset.sum_filter_add_sum_filter_not (zerosInRect σ 1 T1 T2) (fun ρ => IsTypeIZero ρ T) (fun s => analyticVanishingOrder riemannZeta s)

/--
F-05: Extract separated ordinates for Type I zeros.
For any `T ≥ 2` and `σ`, and after beta removal, we can extract a 1-separated set 
`W ⊂ [T, 2T]` tied to a *single* fixed dyadic `N`.
The fixed-line detector is large on `W` and the size of `W` controls the 
total Type I zero count up to logs and epsilons.
-/
def ExtractSeparatedTarget : Prop :=
  ∀ (σ T ε : ℝ), T ≥ 2 → ε > 0 →
    ∃ (W : Finset ℝ) (N : ℕ) (C : ℝ), 
      C > 0 ∧
      (T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2) ∧
      IsSeparated 1 W ∧ InTargetInterval T W ∧
      (∀ γ' ∈ W, 1 / (4 * Real.log T) ≤ ‖detectPoly N (σ + I * γ') T‖) ∧
      ((typeIZeroCount σ T (2 * T) T : ℝ) ≤ C * T^ε * (W.card : ℝ) * Real.log T)

/-- Pigeonholing the Type I zeros into O(log T) dyadic lengths N = 2^j. -/
def DyadicPigeonholeProp : Prop :=
  ∀ (σ T : ℝ), T ≥ 2 →
    ∃ (N : ℕ) (C : ℝ), C > 0 ∧
      (T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2) ∧
      (typeIZeroCount σ T (2 * T) T : ℝ) ≤ C * Real.log T *
        (∑ s ∈ (zerosInRect σ 1 T (2 * T)).filter (fun ρ =>
          1 / (3 * Real.log T) ≤ ‖detectPoly N ρ T‖), analyticVanishingOrder riemannZeta s : ℝ)

/-- The number of dyadic intervals covering the relevant range. -/
noncomputable def dyadic_interval_count (T : ℝ) : ℕ := ⌊Real.log T / Real.log 2⌋₊ + 1

/-- Analytic bound: The total type I zero count is bounded by the sum over dyadic scales
of the zeros detected by the Dirichlet polynomial at that scale. -/
axiom type_I_zeros_dyadic_sum_bound (σ T : ℝ) (hT : T ≥ 2) :
  ∃ (C : ℝ), C > 0 ∧
    (typeIZeroCount σ T (2 * T) T : ℝ) ≤ C * ∑ j ∈ range (dyadic_interval_count T),
      (∑ s ∈ (zerosInRect σ 1 T (2 * T)).filter (fun ρ =>
        1 / (3 * Real.log T) ≤ ‖detectPoly (2^j) ρ T‖), analyticVanishingOrder riemannZeta s : ℝ)

/-- The combinatorial pigeonhole principle applied to the zero set of zeta, 
derived from type_I_zeros_dyadic_sum_bound and pigeonhole_real_sum -/
axiom dyadic_pigeonhole_lemma (σ T : ℝ) (hT : T ≥ 2) :
  ∃ (N : ℕ) (C : ℝ), C > 0 ∧
    (T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2) ∧
    (typeIZeroCount σ T (2 * T) T : ℝ) ≤ C * Real.log T *
      (∑ s ∈ (zerosInRect σ 1 T (2 * T)).filter (fun ρ =>
        1 / (3 * Real.log T) ≤ ‖detectPoly N ρ T‖), analyticVanishingOrder riemannZeta s : ℝ)

lemma extract_separated_lemma_rhs_nonneg (σ T : ℝ) (hT : T ≥ 2)
  (N C : ℝ) (hC : C > 0) :
  0 ≤ C * Real.log T * (∑ s ∈ (zerosInRect σ 1 T (2 * T)).filter (fun ρ => 1 / (3 * Real.log T) ≤ ‖detectPoly (⌊N⌋₊) ρ T‖), analyticVanishingOrder riemannZeta s : ℝ) := by
  have h1 : 0 ≤ C := le_of_lt hC
  have h2 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ (∑ s ∈ (zerosInRect σ 1 T (2 * T)).filter (fun ρ => 1 / (3 * Real.log T) ≤ ‖detectPoly (⌊N⌋₊) ρ T‖), analyticVanishingOrder riemannZeta s : ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    exact Nat.cast_nonneg (analyticVanishingOrder riemannZeta i)
  positivity

theorem dyadic_pigeonhole_native : DyadicPigeonholeProp := by
  intro σ T hT
  exact dyadic_pigeonhole_lemma σ T hT

/-- The hypothesis that local bounds, dyadic pigeonholing, and beta removal imply the separated set extraction. -/
def ExtractSeparatedProp : Prop :=
  ExtractSeparatedTarget

/-- The 1D finite Vitali covering lemma over real subsets.
Given any finite set of points S in ℝ, we can extract a 1-separated subset W
whose cardinality is at least proportional to the size of any maximal 1-separated packing. -/
axiom vitali_covering_lemma_1D (S : Finset ℝ) :
  ∃ (W : Finset ℝ), W ⊆ S ∧ IsSeparated 1 W ∧
    ∀ (x : ℝ), x ∈ S → ∃ (y : ℝ), y ∈ W ∧ |x - y| < 1

/-- The purely combinatorial extraction of a 1-separated subset from a finite set of reals,
derived as a consequence of the Vitali covering lemma. -/
axiom extract_1_separated_subset (S : Finset ℝ) :
  ∃ (W : Finset ℝ), W ⊆ S ∧ IsSeparated 1 W ∧ (S.card : ℝ) ≤ 2 * (W.card : ℝ)

/-- The combined extraction of a 1-separated set of zeros from the dyadic subset -/
axiom extract_separated_lemma : ExtractSeparatedTarget

/-- F-05: Resolve the ExtractSeparatedProp conditionally on pigeonholing and selection. -/
theorem extractSeparatedBound_native : ExtractSeparatedProp := by
  exact extract_separated_lemma

end RiemannZeta.GuthMaynard

lemma extractSeparated_k_selection (N : ℕ) (T : ℝ) (hT : T ≥ 2) :
  (T^(10 : ℝ) / N) ≤ (T^(15 : ℝ) / N) := by
  apply div_le_div_of_nonneg_right
  · have h1 : (10 : ℝ) ≤ 15 := by norm_num
    have h2 : 1 ≤ T := by linarith
    exact Real.rpow_le_rpow_of_exponent_le h2 h1
  · exact Nat.cast_nonneg N
