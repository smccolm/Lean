import GafniTao.FordLemma32Source
import Mathlib.NumberTheory.PrimeCounting

/-!
# Ford's set of the first `k^3` primes above `M`

The source does not choose an arbitrary prime packet: it uses the `k^3`
smallest primes strictly larger than `M`.  This file gives that packet a
canonical finite definition and proves the properties consumed by Lemma 3.2.
-/

namespace GafniTao

noncomputable section

def FordPrimeAbove (M p : ℕ) : Prop := M < p ∧ Nat.Prime p

theorem fordPrimeAbove_infinite (M : ℕ) :
    {p : ℕ | FordPrimeAbove M p}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hpLower, hpPrime⟩ := Nat.exists_infinite_primes (max M n + 1)
  refine ⟨p, ⟨?_, hpPrime⟩, ?_⟩ <;> omega

/-- The canonical set of the `k^3` smallest primes greater than `M`. -/
def fordPrimeSet (k M : ℕ) : Finset ℕ :=
  (Finset.range (k ^ 3)).image (Nat.nth (FordPrimeAbove M))

theorem fordPrimeSet_card (k M : ℕ) :
    (fordPrimeSet k M).card = k ^ 3 := by
  unfold fordPrimeSet
  rw [Finset.card_image_of_injective _
    (Nat.nth_injective (fordPrimeAbove_infinite M)), Finset.card_range]

theorem fordPrimeSet_mem_source {k M p : ℕ}
    (hp : p ∈ fordPrimeSet k M) : M < p ∧ Nat.Prime p := by
  rw [fordPrimeSet, Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact Nat.nth_mem_of_infinite (fordPrimeAbove_infinite M) i

theorem fordPrimeSet_prime {k M p : ℕ}
    (hp : p ∈ fordPrimeSet k M) : Nat.Prime p :=
  (fordPrimeSet_mem_source hp).2

theorem fordPrimeSet_gt {k M p : ℕ}
    (hp : p ∈ fordPrimeSet k M) : M < p :=
  (fordPrimeSet_mem_source hp).1

/-- Literal specialization of Ford Lemma 3.2 to its canonical packet of the
`k^3` smallest primes above `M`. -/
theorem ford_lemma_3_2_canonical_prime_set
    {k d T P s Q q r M : ℕ}
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk4 : 4 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdr : d < r) (hds : d + 1 ≤ s)
    (hM : k ≤ M) (hPM : P ≤ M ^ (k + 1)) (hMP : M ^ r ≤ P)
    (hQ : 32 * s ^ 2 * M < Q) (hQP : Q ≤ P)
    (hq : 0 < q) (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (hpacket : ∀ p ∈ fordPrimeSet k M, p ≤ 2 * M) :
    ∃ (Ψ : FordIntegerPolynomialSystem k d T) (p : ℕ),
      p ∈ fordPrimeSet k M ∧
      ∃ c : ZMod p,
        fordKCount Ψ₀ s P Q q ≤
          4 * k ^ 3 * k.factorial *
            p ^ ((2 * s - d) +
              ((r - d - 1) * (r - d) / 2 + r * d)) *
            fordLCount
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P (Q / p) p q r := by
  exact ford_lemma_3_2_nat_endpoints (fordPrimeSet k M) Ψ₀ hk4 hr2 hrk
    hdr hds hM hPM hMP hQ hQP hq hTpos hT (fordPrimeSet_card k M)
    (fun p hp => fordPrimeSet_prime hp)
    (fun p hp => ⟨fordPrimeSet_gt hp, hpacket p hp⟩)

#print axioms fordPrimeAbove_infinite
#print axioms fordPrimeSet_card
#print axioms fordPrimeSet_mem_source
#print axioms ford_lemma_3_2_canonical_prime_set

end

end GafniTao
