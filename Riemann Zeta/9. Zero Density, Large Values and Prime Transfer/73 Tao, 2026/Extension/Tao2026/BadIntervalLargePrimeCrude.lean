import Tao2026.BadIntervalLargePrimeProductCollision
import Mathlib.Data.Int.CardIntervalMod

/-!
# Arithmetic progression input for the large-prime crude bounds

This module starts the direct finite counting proof of the crude parts of
Propositions 6.7--6.8.  It defines the primes in a dyadic band lying in one
residue class and bounds their cardinality by the exact elementary progression
majorant `⌊2Z/q⌋ + 1`.  This is the coordinate-fiber estimate used after the
remaining tuple coordinates are frozen.
-/

namespace Tao2026

open scoped Classical

/-- The prime-band fiber in the residue class `a mod q`. -/
def taoDyadicPrimeResidueFiber (q a Z : ℕ) : Finset ℕ :=
  (taoDyadicPrimeBand Z).filter fun n => n ≡ a [MOD q]

/-- A residue class modulo positive `q` occupies at most `⌊2Z/q⌋+1` points
of the entire interval `[0,2Z)`, hence no more primes in `[Z,2Z)`. -/
theorem card_taoDyadicPrimeResidueFiber_le
    {q a Z : ℕ} (hq : 0 < q) :
    (taoDyadicPrimeResidueFiber q a Z).card ≤ (2 * Z) / q + 1 := by
  calc
    (taoDyadicPrimeResidueFiber q a Z).card ≤
        ((Finset.range (2 * Z)).filter fun n => n ≡ a [MOD q]).card := by
      apply Finset.card_le_card
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr
          (mem_taoDyadicPrimeBand.mp hnData.1).2.2,
        hnData.2⟩
    _ = (2 * Z).count (fun n => n ≡ a [MOD q]) := by
      rw [Nat.count_eq_card_filter_range]
    _ = (2 * Z) / q + if a % q < (2 * Z) % q then 1 else 0 := by
      exact Nat.count_modEq_card (2 * Z) hq a
    _ ≤ (2 * Z) / q + 1 := by
      split_ifs <;> omega

/-- Real-valued normalized form of the residue-fiber count. -/
theorem card_taoDyadicPrimeResidueFiber_div_band_le
    {q a Z : ℕ} (hq : 0 < q) :
    ((taoDyadicPrimeResidueFiber q a Z).card : ℝ) /
        (taoDyadicPrimeBand Z).card ≤
      (((2 * Z) / q + 1 : ℕ) : ℝ) /
        (taoDyadicPrimeBand Z).card := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast card_taoDyadicPrimeResidueFiber_le (a := a) (Z := Z) hq)
    (Nat.cast_nonneg _)

end Tao2026
