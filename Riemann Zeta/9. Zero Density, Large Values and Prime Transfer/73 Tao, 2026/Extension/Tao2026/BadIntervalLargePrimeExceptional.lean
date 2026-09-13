import Tao2026.BadIntervalLargePrimeCharacter
import Tao2026.ExceptionalCharacterAggregate

/-!
# Exceptional large-prime conductors

This module extracts the conductor-count consequence of the Burgess-conditional
Lemma 5.1 for Proposition 6.7.  In an admissible large-prime interval, a
conductor is exceptional when it supports at least one primitive character
whose normalized prime-band sum crosses Tao's exact threshold.  The number of
such conductors is at most the total exceptional-character count and hence is
`O(Z^(2/125))` under the explicit Burgess input.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

def taoLargePrimeExceptionalConductorsIn (D : Finset ℕ) (Z : ℕ) : Finset ℕ :=
  D.filter fun q => (taoExceptionalPrimitiveCharacters q Z).Nonempty

theorem taoLargePrimeExceptionalConductorsIn_subset (D : Finset ℕ) (Z : ℕ) :
    taoLargePrimeExceptionalConductorsIn D Z ⊆ D := by
  exact Finset.filter_subset _ _

theorem card_taoLargePrimeExceptionalConductorsIn_le_sum_card
    (D : Finset ℕ) (Z : ℕ) :
    (taoLargePrimeExceptionalConductorsIn D Z).card ≤
      ∑ q ∈ D, (taoExceptionalPrimitiveCharacters q Z).card := by
  calc
    (taoLargePrimeExceptionalConductorsIn D Z).card =
        ∑ q ∈ taoLargePrimeExceptionalConductorsIn D Z, 1 := by simp
    _ ≤ ∑ q ∈ taoLargePrimeExceptionalConductorsIn D Z,
        (taoExceptionalPrimitiveCharacters q Z).card := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.one_le_card.mpr (Finset.mem_filter.mp hq).2
    _ ≤ ∑ q ∈ D, (taoExceptionalPrimitiveCharacters q Z).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoLargePrimeExceptionalConductorsIn_subset D Z) (fun _ _ _ => Nat.zero_le _)

theorem isAdmissible_taoLargeAntiSievePrimeRange
    {lowerPrime upperPrime Z : ℕ}
    (hrange : (upperPrime : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    IsAdmissibleTaoExceptionalConductorSet
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) Z := by
  constructor
  · intro p hp
    exact (mem_taoLargeAntiSievePrimeRange.mp hp).1.squarefree
  · intro p hp
    calc
      (p : ℝ) ≤ (upperPrime : ℝ) := by
        exact_mod_cast (mem_taoLargeAntiSievePrimeRange.mp hp).2.2
      _ ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent) := hrange

theorem exists_eventually_card_taoLargePrimeExceptionalConductors_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (lowerPrime upperPrime : ℕ → ℕ)
    (hrange : ∀ᶠ Z : ℕ in atTop, (upperPrime Z : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      ((taoLargePrimeExceptionalConductorsIn
        (taoLargeAntiSievePrimeRange (lowerPrime Z) (upperPrime Z)) Z).card : ℝ) ≤
          K * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  let D : ℕ → Finset ℕ := fun Z =>
    taoLargeAntiSievePrimeRange (lowerPrime Z) (upperPrime Z)
  have hD : ∀ᶠ Z : ℕ in atTop,
      IsAdmissibleTaoExceptionalConductorSet (D Z) Z := by
    filter_upwards [hrange] with Z hZ
    exact isAdmissible_taoLargeAntiSievePrimeRange hZ
  obtain ⟨K, hK, hcard, hmoment⟩ :=
    exists_eventually_conductorExceptional_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess D hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard] with Z hZ
  change ((taoLargePrimeExceptionalConductorsIn (D Z) Z).card : ℝ) ≤ _
  calc
    ((taoLargePrimeExceptionalConductorsIn (D Z) Z).card : ℝ) ≤
        ((∑ q ∈ D Z, (taoExceptionalPrimitiveCharacters q Z).card : ℕ) : ℝ) := by
      exact_mod_cast card_taoLargePrimeExceptionalConductorsIn_le_sum_card (D Z) Z
    _ ≤ K * (Z : ℝ) ^ (2 / 125 : ℝ) := hZ

end

end Tao2026


