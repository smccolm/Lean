import Dubon2026.DirichletPolynomial
import Mathlib.Data.Nat.Factorization.Basic

/-! # The finite prime coordinates of the actual Dirichlet polynomial

Coordinates are indexed by the primes at most `N`, rather than by an unrelated
finite type. The exponent of each coordinate is the actual prime valuation.
-/

namespace Dubon2026

open scoped BigOperators

noncomputable section

/-- All prime coordinate indices at most the truncation length. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

theorem mem_primesUpTo {p N : ℕ} : p ∈ primesUpTo N ↔ p.Prime ∧ p ≤ N := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact and_comm

/-- The actual finite type of primes used by the Bohr lift. -/
abbrev PrimeCoordinate (N : ℕ) := ↥(primesUpTo N)

theorem factorization_support_subset_primesUpTo {n N : ℕ} (hn : n ≤ N) :
    n.factorization.support ⊆ primesUpTo N := by
  intro p hp
  rw [Nat.support_factorization] at hp
  exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (Nat.le_of_mem_primeFactors hp).trans hn⟩

theorem factorization_eq_zero_outside {n N p : ℕ} (hn : n ≤ N)
    (hp : p ∉ primesUpTo N) : n.factorization p = 0 := by
  apply Finsupp.notMem_support_iff.mp
  exact fun h => hp (factorization_support_subset_primesUpTo hn h)

theorem prime_exponent_vector_injective {m n N : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N)
    (h : ∀ p : PrimeCoordinate N, m.factorization p.val = n.factorization p.val) :
    m = n := by
  apply Nat.eq_of_factorization_eq (by omega) (by omega)
  intro p
  by_cases hp : p ∈ primesUpTo N
  · exact h ⟨p, hp⟩
  · rw [factorization_eq_zero_outside hmN hp, factorization_eq_zero_outside hnN hp]

theorem log_eq_sum_prime_coordinates {n N : ℕ} (hn : n ≤ N) :
    Real.log n = ∑ p : PrimeCoordinate N, (n.factorization p.val : ℝ) * Real.log p.val := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  change _ = ∑ p : ↥(primesUpTo N), (n.factorization p.val : ℝ) * Real.log p.val
  rw [Finset.sum_coe_sort (primesUpTo N) (fun p : ℕ => (n.factorization p : ℝ) * Real.log p)]
  apply Finset.sum_subset (factorization_support_subset_primesUpTo hn)
  intro p _ hp
  rw [Finsupp.notMem_support_iff.mp hp, Nat.cast_zero, zero_mul]

/-- The genuine monomial determined by the factorization vector. -/
def bohrMonomial (N n : ℕ) (z : PrimeCoordinate N → ℂ) : ℂ :=
  ∏ p : PrimeCoordinate N, z p ^ n.factorization p.val

/-- The finite Bohr polynomial, defined on all complex coordinates before restriction to the torus. -/
def bohrLift (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeCoordinate N → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(σ : ℂ)) * bohrMonomial N n z

/-- The multiplicative torus flow with the source's negative frequency convention. -/
def verticalFlow (N : ℕ) (t : ℝ) (p : PrimeCoordinate N) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * (Real.log p.val : ℂ))

theorem bohrMonomial_verticalFlow {n N : ℕ} (hn : n ≤ N) (t : ℝ) :
    bohrMonomial N n (verticalFlow N t) =
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
  unfold bohrMonomial verticalFlow
  simp only [← Complex.exp_nat_mul, ← Complex.exp_sum]
  congr 1
  have hlog : (Real.log n : ℂ) =
      ∑ p : PrimeCoordinate N, (n.factorization p.val : ℂ) * (Real.log p.val : ℂ) := by
    exact_mod_cast log_eq_sum_prime_coordinates hn
  rw [hlog, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem bohrLift_verticalFlow (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    bohrLift a N σ (verticalFlow N t) = dirichletSum a N ((σ : ℂ) + Complex.I * t) := by
  rw [bohrLift, dirichletSum_eq_sum_exp]
  apply Finset.sum_congr rfl
  intro n hn
  rw [nat_cpow_neg_eq_exp (Finset.mem_Icc.mp hn).1,
    bohrMonomial_verticalFlow (Finset.mem_Icc.mp hn).2, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end

end Dubon2026
