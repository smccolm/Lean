import GafniTao.FordCompleteCounts

/-!
# Ford Lemma 3.2: prime avoidance

This is the exact finite divisibility pigeonhole used between (3.2) and
(3.3): an integer smaller than the product of a finite set of distinct primes
cannot be divisible by every prime in that set.
-/

open Finset
open scoped BigOperators

namespace GafniTao

theorem ford_prime_set_pairwise_coprime
    {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p) :
    (S : Set ℕ).Pairwise (Function.onFun IsCoprime fun p => (p : ℤ)) := by
  intro p hp q hq hpq
  exact ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq).isCoprime

/-- Integer form, stated through the natural absolute value as in Ford's
Jacobian application. -/
theorem exists_prime_not_dvd_int_of_natAbs_lt_prod
    {S : Finset ℕ} {a : ℤ}
    (hprime : ∀ p ∈ S, Nat.Prime p) (ha : a ≠ 0)
    (hlt : a.natAbs < ∏ p ∈ S, p) :
    ∃ p ∈ S, ¬(p : ℤ) ∣ a := by
  by_contra h
  push Not at h
  have hprod : (∏ p ∈ S, (p : ℤ)) ∣ a := by
    apply Finset.prod_dvd_of_coprime (ford_prime_set_pairwise_coprime hprime)
    exact h
  have habs : (∏ p ∈ S, p) ∣ a.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hprod
    have hprodabs : (∏ p ∈ S, (p : ℤ)).natAbs = ∏ p ∈ S, p := by
      change Int.natAbsHom (∏ p ∈ S, (p : ℤ)) = ∏ p ∈ S, p
      rw [map_prod]
      simp
    rwa [hprodabs] at this
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) habs)) hlt

/-- The natural-number specialization of the prime-selection step. -/
theorem exists_prime_not_dvd_of_lt_prod
    {S : Finset ℕ} {a : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p) (ha : 0 < a)
    (hlt : a < ∏ p ∈ S, p) :
    ∃ p ∈ S, ¬p ∣ a := by
  obtain ⟨p, hpS, hp⟩ := exists_prime_not_dvd_int_of_natAbs_lt_prod
    (a := (a : ℤ)) hprime (Int.ofNat_ne_zero.mpr (ne_of_gt ha))
      (by simpa using hlt)
  refine ⟨p, hpS, ?_⟩
  intro hpa
  apply hp
  exact Int.natCast_dvd_natCast.mpr hpa

#print axioms ford_prime_set_pairwise_coprime
#print axioms exists_prime_not_dvd_of_lt_prod
#print axioms exists_prime_not_dvd_int_of_natAbs_lt_prod

end GafniTao
