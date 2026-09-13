import Tao2026.ExceptionalCharacterCofactorUniform

/-!
# Exceptional large-prime pairs for Proposition 6.8

For a fixed prime `p`, this module takes the remaining primes `p'` from a
prescribed interval, removes `p`, and applies the common-factor form of Tao's
Lemma 5.1 to the primitive characters of conductor `p*p'`.  One absolute
the same bound works eventually for every fixed prime and every interval satisfying
the exact square-root conductor range.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

/-- Prime partners `p'` for which the product conductor `p*p'` supports at
least one exceptional primitive character. -/
def taoLargePrimeExceptionalPartners
    (p lowerPrime upperPrime Z : ℕ) : Finset ℕ :=
  taoExceptionalCofactorsIn p
    ((taoLargeAntiSievePrimeRange lowerPrime upperPrime).erase p) Z

/-- Burgess-conditional exceptional-pair count in the exact common-factor
family shape used by Proposition 6.8. -/
theorem exists_eventually_card_taoLargePrimeExceptionalPartners_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ Z : ℕ in atTop,
      ∀ p lowerPrime upperPrime : ℕ,
        Nat.Prime p →
        (upperPrime : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) →
        ((taoLargePrimeExceptionalPartners p lowerPrime upperPrime Z).card : ℝ) ≤
          A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  obtain ⟨A, hA, huniform⟩ :=
    exists_uniform_eventually_card_taoExceptionalCofactorsIn_le_of_explicitBurgess
      hC hburgess
  refine ⟨A, hA, ?_⟩
  filter_upwards [huniform] with Z hZ p lowerPrime upperPrime hp hrange
  let D := (taoLargeAntiSievePrimeRange lowerPrime upperPrime).erase p
  have hDsq : ∀ q ∈ D, Squarefree q := by
    intro q hq
    exact (mem_taoLargeAntiSievePrimeRange.mp
      (Finset.mem_of_mem_erase hq)).1.squarefree
  have hDcop : ∀ q ∈ D, Nat.Coprime p q := by
    intro q hq
    have hqPrime : Nat.Prime q :=
      (mem_taoLargeAntiSievePrimeRange.mp
        (Finset.mem_of_mem_erase hq)).1
    exact (Nat.coprime_primes hp hqPrime).mpr
      (Finset.ne_of_mem_erase hq).symm
  have hDrange : ∀ q ∈ D, (q : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) := by
    intro q hq
    calc
      (q : ℝ) ≤ (upperPrime : ℝ) := by
        exact_mod_cast (mem_taoLargeAntiSievePrimeRange.mp
          (Finset.mem_of_mem_erase hq)).2.2
      _ ≤ Real.sqrt
          ((Z : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ)) := hrange
  simpa only [taoLargePrimeExceptionalPartners, D] using
    hZ p D hp.pos hp.squarefree hDsq hDcop hDrange

end

end Tao2026
