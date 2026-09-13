import Tao2026.BadIntervalLargePrimeAggregation

/-!
# Resolving exceptional product conductors into prime and pair sets

For distinct primes `p,q`, the nontrivial divisors of `pq` are exactly
`p,q,pq`.  This identifies failure of the product-modulus unexceptionality
predicate with the exceptional prime-conductor unions and the common-factor
exceptional-partner union already controlled by Lemma 5.1.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

theorem prime_pair_divisor_eq
    {p q d : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hd : d ∈ (p * q).divisors) :
    d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  rw [hcop.divisors_mul] at hd
  rcases Finset.mem_map.mp hd with ⟨x, hx, rfl⟩
  have hxmem := x.prop
  change x.val ∈ p.divisors ×ˢ q.divisors at hxmem
  rw [Finset.mem_product] at hxmem
  have hxp : x.val.1 = 1 ∨ x.val.1 = p := by
    simpa [hp.divisors] using hxmem.1
  have hxq : x.val.2 = 1 ∨ x.val.2 = q := by
    simpa [hq.divisors] using hxmem.2
  rcases hxp with hxp | hxp <;> rcases hxq with hxq | hxq <;>
    change x.val.1 * x.val.2 = 1 ∨ x.val.1 * x.val.2 = p ∨
      x.val.1 * x.val.2 = q ∨ x.val.1 * x.val.2 = p * q <;>
    simp [hxp, hxq]

theorem prime_pair_divisors_erase_one
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (p * q).divisors.erase 1 = {p, q, p * q} := by
  ext d
  constructor
  · intro hd
    have hdmem := Finset.mem_of_mem_erase hd
    have hdne := Finset.ne_of_mem_erase hd
    have hclass := prime_pair_divisor_eq hp hq hpq hdmem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hclass.resolve_left hdne
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one]
    · simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hq.ne_one]
    · simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one, hq.ne_one]

/-- Partners exceptional at at least one of the 1000 ordinary coordinate
scales. -/
def taoLargePrimeExceptionalPartnersFor
    (p lowerPrime upperPrime : ℕ) (P : Fin 1001 → ℕ) : Finset ℕ :=
  (Finset.univ.erase (0 : Fin 1001)).biUnion fun j =>
    taoLargePrimeExceptionalPartners p lowerPrime upperPrime (P j)

theorem card_taoLargePrimeExceptionalPartnersFor_le
    (p lowerPrime upperPrime : ℕ) (P : Fin 1001 → ℕ) :
    (taoLargePrimeExceptionalPartnersFor p lowerPrime upperPrime P).card ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (taoLargePrimeExceptionalPartners p lowerPrime upperPrime (P j)).card := by
  exact Finset.card_biUnion_le

theorem card_taoLargePrimeExceptionalPartnersFor_le_thousand_mul
    (p lowerPrime upperPrime : ℕ) (P : Fin 1001 → ℕ) (B : ℕ)
    (hB : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      (taoLargePrimeExceptionalPartners p lowerPrime upperPrime (P j)).card ≤ B) :
    (taoLargePrimeExceptionalPartnersFor p lowerPrime upperPrime P).card ≤
      1000 * B := by
  calc
    (taoLargePrimeExceptionalPartnersFor p lowerPrime upperPrime P).card ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (taoLargePrimeExceptionalPartners p lowerPrime upperPrime (P j)).card :=
      card_taoLargePrimeExceptionalPartnersFor_le p lowerPrime upperPrime P
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001), B := by
      exact Finset.sum_le_sum fun j hj => hB j hj
    _ = 1000 * B := by simp

private theorem not_mem_exceptionalFor_of_not_mem_exceptionalFor
    {D E : Finset ℕ} {q : ℕ} {P : Fin 1001 → ℕ}
    (hqD : q ∈ D)
    (hq : q ∉ taoLargePrimeExceptionalConductorsFor D P) :
    q ∉ taoLargePrimeExceptionalConductorsFor E P := by
  intro hqEbad
  apply hq
  rw [taoLargePrimeExceptionalConductorsFor, Finset.mem_biUnion] at hqEbad ⊢
  rcases hqEbad with ⟨j, hj, hjbad⟩
  refine ⟨j, hj, ?_⟩
  simp only [taoLargePrimeExceptionalConductorsIn, Finset.mem_filter] at hjbad ⊢
  exact ⟨hqD, hjbad.2⟩

/-- If neither prime conductor is exceptional and `q` is not an exceptional
common-factor partner of `p`, then all three nontrivial divisors of `pq` are
unexceptional. -/
theorem taoLargePrimePairUnexceptional_of_prime_and_partner
    {lowerPrime upperPrime : ℕ} (P : Fin 1001 → ℕ)
    (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpD : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hqD : b.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hpGood : a.2 ∉ taoLargePrimeExceptionalConductorsFor
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P)
    (hqGood : b.2 ∉ taoLargePrimeExceptionalConductorsFor
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P)
    (hpqGood : b.2 ∉ taoLargePrimeExceptionalPartnersFor
      a.2 lowerPrime upperPrime P) :
    TaoLargePrimePairUnexceptional P a b := by
  intro d hd
  have hdmem := Finset.mem_of_mem_erase hd
  have hdne := Finset.ne_of_mem_erase hd
  rcases (prime_pair_divisor_eq hp hq hpq hdmem).resolve_left hdne with
    rfl | rfl | rfl
  · exact not_mem_exceptionalFor_of_not_mem_exceptionalFor
      hpD hpGood
  · exact not_mem_exceptionalFor_of_not_mem_exceptionalFor
      hqD hqGood
  · intro hpqBad
    apply hpqGood
    rw [taoLargePrimeExceptionalPartnersFor, Finset.mem_biUnion]
    rw [taoLargePrimeExceptionalConductorsFor, Finset.mem_biUnion] at hpqBad
    rcases hpqBad with ⟨j, hj, hjbad⟩
    refine ⟨j, hj, ?_⟩
    simp only [taoLargePrimeExceptionalPartners,
      taoExceptionalCofactorsIn, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_erase.mpr ⟨hpq.symm, hqD⟩
    · rw [taoLargePrimeExceptionalConductorsIn, Finset.mem_filter] at hjbad
      exact hjbad.2

/-- Contrapositive covering form: every exceptional product pair is charged
to the first prime, the second prime, or the common-factor partner union. -/
theorem exceptional_pair_mem_prime_or_prime_or_partner
    {lowerPrime upperPrime : ℕ} (P : Fin 1001 → ℕ)
    (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpD : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hqD : b.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hbad : ¬TaoLargePrimePairUnexceptional P a b) :
    a.2 ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P ∨
      b.2 ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P ∨
      b.2 ∈ taoLargePrimeExceptionalPartnersFor
        a.2 lowerPrime upperPrime P := by
  by_contra h
  push Not at h
  exact hbad (taoLargePrimePairUnexceptional_of_prime_and_partner
    P a b hp hq hpq hpD hqD h.1 h.2.1 h.2.2)

end

end Tao2026
