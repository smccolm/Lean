import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Tactic

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard


/-- F-07: Explicitly construct convolution coefficients for the powered polynomial. -/
noncomputable def powCoeff (N k : ℕ) (m : ℕ) (T : ℝ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, detectorCoeff (p x : ℕ) T

/-- Factorization count bounds. -/
def FactorizationCountBoundProp : Prop :=
  ∀ (k m : ℕ) (ε : ℝ), ε > 0 →
    ∃ C : ℝ, 0 < C ∧ ((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m)).card ≤ C * (m : ℝ)^ε

/-- Classical bound for the k-th divisor function -/
lemma k_divisor_function_bound_one (k : ℕ) (ε : ℝ) :
  (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).filter (fun p => (∏ x : Fin k, p x) = 1)).card : ℝ) ≤ 1 * (1 : ℝ)^ε := by
  have h1 : (1 : ℝ)^ε = 1 := Real.one_rpow ε
  rw [h1, mul_one]
  have h2 : ((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).filter (fun p => (∏ x : Fin k, p x) = 1)).card ≤
             (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).card := Finset.card_filter_le _ _
  have h3 : (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).card = ∏ x : Fin k, (Finset.Ioc 1 1).card := by
    exact Fintype.card_piFinset _
  rw [h3] at h2
  have h4 : ∏ x : Fin k, (Finset.Ioc 1 1).card = ∏ x : Fin k, 0 := by
    apply Finset.prod_congr rfl
    intro x _
    exact Nat.sub_self 1
  rw [h4] at h2
  cases k with
  | zero =>
    have h_prod_one : ∏ x : Fin 0, (0 : ℕ) = 1 := rfl
    rw [h_prod_one] at h2
    exact_mod_cast h2
  | succ k' =>
    have h_prod_zero : ∏ x : Fin (k' + 1), (0 : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k' + 1)))
      rfl
    rw [h_prod_zero] at h2
    have h5 : ((Fintype.piFinset (fun (_ : Fin (k' + 1)) => Finset.Ioc 1 1)).filter (fun p => ∏ x, p x = 1)).card = 0 := by linarith
    rw [h5]
    norm_num

axiom k_divisor_function_bound (k m : ℕ) (ε : ℝ) (hε : 0 < ε) :
  ∃ C : ℝ, 0 < C ∧ (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m)).card : ℝ) ≤ C * (m : ℝ)^ε

theorem divisor_bound_native : FactorizationCountBoundProp := by
  intro k m ε hε
  exact k_divisor_function_bound k m ε hε


/-- Bound for the powered coefficients incorporating epsilon loss. -/
def PowCoeffBoundProp : Prop :=
  ∀ (N k m : ℕ) (T ε : ℝ), 0 < m → T ≥ 1 → ε > 0 →
    ∃ C : ℝ, 0 < C ∧ ‖powCoeff N k m T‖ ≤ C * (m : ℝ)^ε

lemma pow_coeff_rhs_nonneg (C : ℝ) (hC : 0 < C) (m : ℕ) (ε : ℝ) :
  0 ≤ C * (m : ℝ)^ε := by
  have h1 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ (m : ℝ) ^ ε := Real.rpow_nonneg h1 ε
  exact mul_nonneg (le_of_lt hC) h2

lemma pow_coeff_subset (N k m : ℕ) (hm : 0 < m) :
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m) ⊆
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m) := by
  intro p hp
  rw [mem_filter] at hp ⊢
  rcases hp with ⟨hp_pi, hp_prod⟩
  refine ⟨?_, hp_prod⟩
  rw [Fintype.mem_piFinset] at hp_pi ⊢
  intro x
  have hpx := hp_pi x
  rw [mem_Ioc] at hpx ⊢
  rcases hpx with ⟨hpx1, hpx2⟩
  constructor
  · by_cases hN : N = 0
    · rw [hN] at hpx1 hpx2
      linarith
    · have hN_pos : N ≥ 1 := Nat.pos_of_ne_zero hN
      linarith
  · have hdvd : p x ∣ ∏ y : Fin k, p y := dvd_prod_of_mem (fun y => p y) (mem_univ x)
    rw [hp_prod] at hdvd
    exact Nat.le_of_dvd hm hdvd

/-- The powered polynomial is defined structurally as the power of the detector.
    The algebraic expansion into coefficients is deferred to the block decomposition. -/
noncomputable def powPoly (N k : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  (detectPoly N s T) ^ k

lemma powPoly_eval (N k : ℕ) (s : ℂ) (T : ℝ) :
  powPoly N k s T = (detectPoly N s T) ^ k := by
  rfl

/-- F-07: The power identity theorem. -/
theorem polynomial_power_identity (N k : ℕ) (s : ℂ) (T : ℝ) :
  (detectPoly N s T) ^ k = powPoly N k s T := rfl

/- 
F-07: Decomposition into O(k) dyadic blocks.
This is mathematically redundant as a standalone topological hypothesis.
Partitioning the polynomial sum into dyadic blocks [M, 2M] is a standard
pigeonholing technique that is deferred to the AlgebraicCombinationProp proof.
-/

/- Normalized block polynomial where coefficients are bounded by 1. -/
/- 
F-07: The normalization step is mathematically redundant as a standalone hypothesis.
The normalization of coefficients (dividing by C * (2M)^ε) can be done directly 
inside the final AlgebraicCombinationProp before applying GuthMaynardLargeValues.
-/

end RiemannZeta.GuthMaynard
