import Tao2026.FactorialOneTermAsymptotics

/-!
# Source-facing Erdős--Selfridge reduction

This file records the stronger prime-valuation statement isolated as Theorem 2
of Erdős--Selfridge (1975) and proves that its square specialization supplies
the exact residual input used by Tao's factorial-fiber argument.

The analytic/arithmetic content of Erdős--Selfridge Theorem 2 remains an
explicit proposition.  Everything here is the kernel-checked translation from
that source statement to `ErdosSelfridgeSquareConclusion`.
-/

namespace Tao2026

/-- The local half-open interval convention is exactly the closed interval
`[N+1,N+H]` used in the source theorem. -/
theorem consecutiveProduct_eq_prod_Icc_succ (N H : ℕ) :
    consecutiveProduct N H = ∏ m ∈ Finset.Icc (N + 1) (N + H), m := by
  apply Finset.prod_congr
  · ext m
    simp only [consecutiveInterval, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro m _
    rfl

/-- The least prime greater than or equal to `H`, matching the notation
`p^(H)` in Erdős--Selfridge Theorem 2. -/
noncomputable def erdosSelfridgeNextPrime (H : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes H)

theorem erdosSelfridgeNextPrime_spec (H : ℕ) :
    H ≤ erdosSelfridgeNextPrime H ∧
      (erdosSelfridgeNextPrime H).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes H)

theorem erdosSelfridgeNextPrime_le_of_prime {H p : ℕ}
    (hHp : H ≤ p) (hp : p.Prime) :
    erdosSelfridgeNextPrime H ≤ p := by
  exact Nat.find_min' (Nat.exists_infinite_primes H) ⟨hHp, hp⟩

/-- Source-shaped contract for Erdős--Selfridge Theorem 2.  If the right
endpoint reaches the least prime at least the block length, some prime at
least that length has valuation not divisible by the proposed power. -/
def ErdosSelfridgePrimeMultiplicityConclusion : Prop :=
  ∀ (N H l : ℕ), 3 ≤ H → 2 ≤ l →
    erdosSelfridgeNextPrime H ≤ N + H →
      ∃ p : ℕ, H ≤ p ∧ p.Prime ∧
        ¬l ∣ (consecutiveProduct N H).factorization p

/-- In the residual range `H < N`, Bertrand's postulate makes the endpoint
hypothesis in Erdős--Selfridge Theorem 2 automatic. -/
theorem erdosSelfridgeNextPrime_le_endpoint_of_lt_start
    {N H : ℕ} (hH : 1 ≤ H) (hHN : H < N) :
    erdosSelfridgeNextPrime H ≤ N + H := by
  obtain ⟨p, hp, hHp, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul H (by omega)
  apply (erdosSelfridgeNextPrime_le_of_prime hHp.le hp).trans
  exact hpUpper.trans (by omega)

/-- The `l=2` instance of the source's prime-valuation theorem rules out a
square consecutive product throughout the exact residual range. -/
theorem erdosSelfridgeSquareCoreConclusion_of_primeMultiplicity
    (hES2 : ErdosSelfridgePrimeMultiplicityConclusion) :
    ErdosSelfridgeSquareCoreConclusion := by
  intro N H hH hHN
  rintro ⟨r, hr⟩
  obtain ⟨p, _hHp, _hp, hpOdd⟩ :=
    hES2 N H 2 hH (by omega)
      (erdosSelfridgeNextPrime_le_endpoint_of_lt_start (by omega) hHN)
  apply hpOdd
  rw [hr, Nat.factorization_pow]
  simp

/-- Exact public bridge: Erdős--Selfridge Theorem 2 implies the square
specialization consumed by the factorial-fiber and Theorem 1.10 chain. -/
theorem erdosSelfridgeSquareConclusion_of_primeMultiplicity
    (hES2 : ErdosSelfridgePrimeMultiplicityConclusion) :
    ErdosSelfridgeSquareConclusion :=
  erdosSelfridgeSquareConclusion_of_core
    (erdosSelfridgeSquareCoreConclusion_of_primeMultiplicity hES2)

/-- Public Theorem 1.10 consumer with the Erdős--Selfridge dependency stated
in the stronger source-Theorem-2 form. -/
theorem taoTheorem110_of_lemma42_and_erdosSelfridgePrimeMultiplicity
    (hES2 : ErdosSelfridgePrimeMultiplicityConclusion)
    (h42 : TaoLemma42Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_lemma42_and_erdosSelfridge
    (erdosSelfridgeSquareConclusion_of_primeMultiplicity hES2) h42

/-- Fully source-facing Theorem 1.10 bridge: the prime-valuation theorem,
Tao's Theorem 2.5 input, and Baker--Harman--Pintz supply the public endpoint. -/
theorem taoTheorem110_of_source_inputs_and_primeMultiplicity
    (hES2 : ErdosSelfridgePrimeMultiplicityConclusion)
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) :
    TaoTheorem110Conclusion :=
  taoTheorem110_of_source_inputs_direct
    (erdosSelfridgeSquareConclusion_of_primeMultiplicity hES2) h25 hBHP

end Tao2026
