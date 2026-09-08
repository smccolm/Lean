import Mathlib.Data.Finsupp.Fin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Max

/-!
# Arithmetic anatomy of a natural number

This file fixes the elementary number-theoretic conventions from Tao,
*Products of consecutive integers with unusual anatomy*, Definition 1.2.
In particular, `largestPrimeFactor` is option-valued so that `0` and `1` do
not acquire fictitious largest prime factors.
-/

namespace Tao2026

/-- The largest prime factor of `n`, and `none` when `n` has no prime factor. -/
def largestPrimeFactor (n : ℕ) : Option ℕ :=
  if h : n.primeFactors.Nonempty then some (n.primeFactors.max' h) else none

@[simp]
theorem largestPrimeFactor_eq_none_iff {n : ℕ} :
    largestPrimeFactor n = none ↔ n = 0 ∨ n = 1 := by
  simp [largestPrimeFactor, Nat.nonempty_primeFactors,
    Nat.le_one_iff_eq_zero_or_eq_one]

theorem largestPrimeFactor_eq_some_iff {n p : ℕ} :
    largestPrimeFactor n = some p ↔
      p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors, q ≤ p := by
  simp only [largestPrimeFactor]
  split_ifs with h
  · rw [Option.some_inj]
    exact Finset.max'_eq_iff n.primeFactors h p
  · constructor
    · intro hnone
      cases hnone
    · intro hp
      exact (h ⟨p, hp.1⟩).elim

/-- A natural number is powerful (squarefull) when every prime divisor occurs
with exponent at least two. This deliberately makes `1` powerful and `0`
powerful, matching the literal divisibility predicate; later interval theorems
carry their own positivity hypotheses. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The squarefree component `s(n)`: the product of prime factors occurring
to odd exponent. For positive `n`, this is the largest natural number of the
form `n / m^2` which is squarefree. -/
def squarefreeComponent (n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support.filter (fun p => Odd (n.factorization p)), p

@[simp]
theorem squarefreeComponent_zero : squarefreeComponent 0 = 1 := by
  simp [squarefreeComponent]

@[simp]
theorem squarefreeComponent_one : squarefreeComponent 1 = 1 := by
  simp [squarefreeComponent]

private theorem squarefree_finsetProduct_of_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (s.prod id) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hp ih =>
      have hprime : p.Prime := hs p (by simp)
      have hsprime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have hcoprime : p.Coprime (s.prod id) := by
        rw [hprime.coprime_iff_not_dvd]
        intro hpdvd
        obtain ⟨q, hq, hpq⟩ := (hprime.prime.dvd_finsetProd_iff id).mp hpdvd
        have hqp : q = p := ((hsprime q hq).dvd_iff_eq hprime.ne_one).mp hpq
        exact hp (hqp ▸ hq)
      rw [Finset.prod_insert hp]
      simpa only [id_eq] using
        (Nat.squarefree_mul hcoprime).mpr ⟨hprime.squarefree, ih hsprime⟩

/-- The factorization-parity definition always produces a squarefree number. -/
theorem squarefree_squarefreeComponent (n : ℕ) : Squarefree (squarefreeComponent n) := by
  apply squarefree_finsetProduct_of_primes
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)

/-- The squarefree component uses only prime factors of the original number. -/
theorem squarefreeComponent_dvd (n : ℕ) : squarefreeComponent n ∣ n := by
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
  simpa [squarefreeComponent] using Nat.prod_primeFactors_dvd n

/-- Prime support of the squarefree component is exactly the odd-valuation
support of `n`. -/
theorem mem_primeFactors_squarefreeComponent_iff {n p : ℕ} :
    p ∈ (squarefreeComponent n).primeFactors ↔
      p ∈ n.primeFactors ∧ Odd (n.factorization p) := by
  have hprime : ∀ q ∈ n.factorization.support.filter
      (fun q => Odd (n.factorization q)), q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)
  rw [squarefreeComponent, Nat.primeFactors_prod hprime]
  simp

/-- Valuation form of powerfulness for nonzero naturals. -/
theorem powerful_iff_factorization_two_le {n : ℕ} (hn : n ≠ 0) :
    Powerful n ↔ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
  constructor
  · intro h p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact (hprime.pow_dvd_iff_le_factorization hn).mp
      (h p hprime (Nat.dvd_of_mem_primeFactors hp))
  · intro h p hprime hpdvd
    exact (hprime.pow_dvd_iff_le_factorization hn).mpr
      (h p (hprime.mem_primeFactors hpdvd hn))

end Tao2026
