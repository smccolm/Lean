import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-- Source-faithful general factorization-count input. The constant may depend
    on `k` and `ε`, but is uniform in the positive target `m`. -/
def FactorizationCountBoundProp : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
        (fun p => (∏ x : Fin k, p x) = m)).card : ℝ) ≤ C * (m : ℝ) ^ ε

/-- Source-faithful powered-coefficient bound. Its constant may depend on `k`
    and `ε`, but is uniform in `N`, positive `m`, and `T ≥ 1`. -/
def PowCoeffBoundProp : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ (N m : ℕ) (T : ℝ),
      0 < m → 1 ≤ T → ‖powCoeff N k m T‖ ≤ C * (m : ℝ) ^ ε

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

/-- F-07: The powered convolution coefficients have epsilon-power growth,
    conditionally on the two strictly narrower classical arithmetic inputs. -/
theorem powCoeff_bound_of_uniform_detector_and_factorization
    (hDetector : UniformDetectorCoeffBoundProp)
    (hFactorization : FactorizationCountBoundProp) :
    PowCoeffBoundProp := by
  intro k ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨A, hA, hDetectorA⟩ := hDetector δ hδ
  obtain ⟨B, hB, hFactorB⟩ := hFactorization k δ hδ
  refine ⟨B * A ^ k, mul_pos hB (pow_pos hA k), ?_⟩
  intro N m T hm hT
  let source := (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter
    (fun p => (∏ x : Fin k, p x) = m)
  let target := (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
    (fun p => (∏ x : Fin k, p x) = m)
  have hsource : source ⊆ target := by
    simpa [source, target] using pow_coeff_subset N k m hm
  have hterm (p : Fin k → ℕ) (hp : p ∈ source) :
      ‖∏ x : Fin k, detectorCoeff (p x) T‖ ≤ A ^ k * (m : ℝ) ^ δ := by
    rw [norm_prod]
    have hp_source := hp
    change p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter
      (fun p => (∏ x : Fin k, p x) = m) at hp_source
    rw [mem_filter] at hp_source
    rcases hp_source with ⟨hp_pi, hp_prod⟩
    rw [Fintype.mem_piFinset] at hp_pi
    calc
      ∏ x : Fin k, ‖detectorCoeff (p x) T‖
          ≤ ∏ x : Fin k, A * (p x : ℝ) ^ δ := by
            apply Finset.prod_le_prod
            · intro x _
              exact norm_nonneg _
            · intro x _
              have hpx : 0 < p x :=
                lt_of_le_of_lt (Nat.zero_le N) (mem_Ioc.mp (hp_pi x)).1
              exact hDetectorA (p x) T hpx hT
      _ = (∏ _x : Fin k, A) * (∏ x : Fin k, (p x : ℝ) ^ δ) := by
            rw [Finset.prod_mul_distrib]
      _ = A ^ k * (m : ℝ) ^ δ := by
            rw [Real.finset_prod_rpow Finset.univ (fun x => (p x : ℝ))]
            · have hp_prod_real : ∏ x : Fin k, (p x : ℝ) = (m : ℝ) := by
                exact_mod_cast hp_prod
              rw [hp_prod_real]
              simp
            · intro x _
              positivity
  rw [powCoeff]
  calc
    ‖∑ p ∈ source, ∏ x : Fin k, detectorCoeff (p x) T‖
        ≤ ∑ p ∈ source, ‖∏ x : Fin k, detectorCoeff (p x) T‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _p ∈ source, A ^ k * (m : ℝ) ^ δ := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (source.card : ℝ) * (A ^ k * (m : ℝ) ^ δ) := by simp
    _ ≤ (target.card : ℝ) * (A ^ k * (m : ℝ) ^ δ) := by
      gcongr
    _ ≤ (B * (m : ℝ) ^ δ) * (A ^ k * (m : ℝ) ^ δ) := by
      gcongr
      simpa [target] using hFactorB m hm
    _ = (B * A ^ k) * (m : ℝ) ^ ε := by
      have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
      calc
        B * (m : ℝ) ^ δ * (A ^ k * (m : ℝ) ^ δ) =
            (B * A ^ k) * ((m : ℝ) ^ δ * (m : ℝ) ^ δ) := by ring
        _ = (B * A ^ k) * (m : ℝ) ^ (δ + δ) := by
          rw [Real.rpow_add hmreal]
        _ = (B * A ^ k) * (m : ℝ) ^ ε := by
          congr 2
          dsimp [δ]
          ring

/-- The powered-coefficient bound follows from the classical divisor-count
    estimate and the source-faithful factorization-count estimate. -/
theorem powCoeff_bound_of_divisor_and_factorization
    (hDivisor : DivisorCountBoundProp)
    (hFactorization : FactorizationCountBoundProp) :
    PowCoeffBoundProp :=
  powCoeff_bound_of_uniform_detector_and_factorization
    (uniformDetectorCoeffBound_of_divisorCount hDivisor) hFactorization

/-- The powered polynomial, defined structurally as a power of the detector. -/
noncomputable def powPoly (N k : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  (detectPoly N s T) ^ k

lemma powPoly_eval (N k : ℕ) (s : ℂ) (T : ℝ) :
  powPoly N k s T = (detectPoly N s T) ^ k := by
  rfl

/-- Complex powers of a finite product of natural numbers factor coordinatewise. -/
lemma prod_natCast_cpow_eq {k : ℕ} (p : Fin k → ℕ) (s : ℂ) :
    (∏ x : Fin k, (p x : ℂ) ^ s) = ((∏ x : Fin k, p x : ℕ) : ℂ) ^ s := by
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- A tuple supported on `(N, 2N]` has product supported on `[N^k, (2N)^k]`.
    This includes the empty-product case `k = 0`. -/
lemma powCoeff_product_mem_support (N k : ℕ) (p : Fin k → ℕ)
    (hp : p ∈ Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))) :
    (∏ x : Fin k, p x) ∈ Finset.Icc (N ^ k) ((2 * N) ^ k) := by
  rw [Fintype.mem_piFinset] at hp
  rw [Finset.mem_Icc]
  constructor
  · calc
      N ^ k = ∏ _x : Fin k, N := by simp
      _ ≤ ∏ x : Fin k, p x := by
        apply Finset.prod_le_prod
        · intro _x _
          exact Nat.zero_le N
        · intro x _
          exact (Finset.mem_Ioc.mp (hp x)).1.le
  · calc
      ∏ x : Fin k, p x ≤ ∏ _x : Fin k, 2 * N := by
        apply Finset.prod_le_prod
        · intro x _
          exact Nat.zero_le (p x)
        · intro x _
          exact (Finset.mem_Ioc.mp (hp x)).2
      _ = (2 * N) ^ k := by simp

/-- F-07: Expanding the structural power and collecting tuples by their product
    gives exactly the explicit convolution coefficients `powCoeff`. -/
theorem polynomial_power_identity (N k : ℕ) (s : ℂ) (T : ℝ) :
    powPoly N k s T =
      ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        powCoeff N k m T * (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))
  have hsupport : ∀ p ∈ tuples,
      (∏ x : Fin k, p x) ∈ Finset.Icc (N ^ k) ((2 * N) ^ k) := by
    intro p hp
    exact powCoeff_product_mem_support N k p hp
  rw [powPoly, detectPoly, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ x : Fin k, (detectorCoeff (p x) T * (p x : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ x : Fin k, (detectorCoeff (p x) T * (p x : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ x : Fin k, detectorCoeff (p x) T) *
            ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        ∑ p ∈ tuples with (∏ x : Fin k, p x) = m,
          (∏ x : Fin k, detectorCoeff (p x) T) *
            ((∏ x : Fin k, p x : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Finset.Icc (N ^ k) ((2 * N) ^ k),
        powCoeff N k m T * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [powCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

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
