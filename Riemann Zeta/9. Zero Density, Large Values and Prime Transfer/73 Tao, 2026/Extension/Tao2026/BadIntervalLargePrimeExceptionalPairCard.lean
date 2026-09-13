import Tao2026.BadIntervalLargePrimeCovarianceBlockSum

/-!
# Exceptional modulus-pair cardinality

This module turns the conductor-level covering for Proposition 6.8 into a
cardinality bound for the exact ordered pair finset used by the two-band
covariance sum.  The three terms are the exceptional first endpoints, the
exceptional second endpoints, and the common-factor exceptional partners.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

private theorem card_taoLargePrime_partnerPairs_eq
    (P : Fin 1001 → ℕ) (R S lowerPrime upperPrime : ℕ) :
    (((taoDyadicPrimeBand R).product (taoDyadicPrimeBand S)).filter fun pq =>
      pq.2 ∈ taoLargePrimeExceptionalPartnersFor
        pq.1 lowerPrime upperPrime P).card =
      ∑ p ∈ taoDyadicPrimeBand R,
        ((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeExceptionalPartnersFor
            p lowerPrime upperPrime P).card := by
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  rw [show (∑ pq ∈ (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S),
      if pq.2 ∈ taoLargePrimeExceptionalPartnersFor
          pq.1 lowerPrime upperPrime P then 1 else 0) =
      ∑ p ∈ taoDyadicPrimeBand R, ∑ q ∈ taoDyadicPrimeBand S,
        if q ∈ taoLargePrimeExceptionalPartnersFor
            p lowerPrime upperPrime P then 1 else 0 by
    exact Finset.sum_product _ _ _]
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Exact three-family cardinality bound for exceptional ordered modulus
pairs in two dyadic bands.  The ambient conductor range may be any range
containing both bands. -/
theorem card_taoLargePrimeExceptionalModuliPairs_le
    (P : Fin 1001 → ℕ) (R S lowerPrime upperPrime : ℕ)
    (hR : taoDyadicPrimeBand R ⊆
      taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hS : taoDyadicPrimeBand S ⊆
      taoLargeAntiSievePrimeRange lowerPrime upperPrime) :
    (taoLargePrimeExceptionalModuliPairs P R S).card ≤
      (((taoDyadicPrimeBand R).filter fun p =>
          p ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card *
        (taoDyadicPrimeBand S).card) +
      ((taoDyadicPrimeBand R).card *
        ((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card) +
      ∑ p ∈ taoDyadicPrimeBand R,
        ((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeExceptionalPartnersFor
            p lowerPrime upperPrime P).card := by
  let DR := taoDyadicPrimeBand R
  let DS := taoDyadicPrimeBand S
  let D := taoLargeAntiSievePrimeRange lowerPrime upperPrime
  let ER := DR.filter fun p =>
    p ∈ taoLargePrimeExceptionalConductorsFor D P
  let ES := DS.filter fun q =>
    q ∈ taoLargePrimeExceptionalConductorsFor D P
  let PartnerPairs := (DR.product DS).filter fun pq =>
    pq.2 ∈ taoLargePrimeExceptionalPartnersFor
      pq.1 lowerPrime upperPrime P
  have hsubset : taoLargePrimeExceptionalModuliPairs P R S ⊆
      ((ER.product DS ∪ DR.product ES) ∪ PartnerPairs) := by
    intro pq hpq
    have hpqData := Finset.mem_filter.mp hpq
    have hbands := Finset.mem_product.mp hpqData.1
    have hpData := mem_taoDyadicPrimeBand.mp hbands.1
    have hqData := mem_taoDyadicPrimeBand.mp hbands.2
    have hcover := exceptional_pair_mem_prime_or_prime_or_partner
      P (0, pq.1) (0, pq.2) hpData.1 hqData.1 hpqData.2.1
        (hR hbands.1) (hS hbands.2) hpqData.2.2
    rcases hcover with hpBad | hqBad | hpartner
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hbands.1, hpBad⟩, hbands.2⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_product.mpr
        ⟨hbands.1, Finset.mem_filter.mpr ⟨hbands.2, hqBad⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hpqData.1, hpartner⟩
  have houter := Finset.card_union_le (ER.product DS ∪ DR.product ES) PartnerPairs
  have hinner := Finset.card_union_le (ER.product DS) (DR.product ES)
  have hcard : (taoLargePrimeExceptionalModuliPairs P R S).card ≤
      (ER.product DS).card + (DR.product ES).card + PartnerPairs.card := by
    calc
      (taoLargePrimeExceptionalModuliPairs P R S).card ≤
          ((ER.product DS ∪ DR.product ES) ∪ PartnerPairs).card :=
        Finset.card_le_card hsubset
      _ ≤ (ER.product DS ∪ DR.product ES).card + PartnerPairs.card := houter
      _ ≤ (ER.product DS).card + (DR.product ES).card + PartnerPairs.card := by
        omega
  rw [show (ER.product DS).card = ER.card * DS.card by
        exact Finset.card_product ER DS,
      show (DR.product ES).card = DR.card * ES.card by
        exact Finset.card_product DR ES] at hcard
  simpa only [ER, ES, DR, DS, D, PartnerPairs,
    card_taoLargePrime_partnerPairs_eq] using hcard

/-- Real-valued uniform form of the three-family bound.  This is the direct
interface for the eventual Burgess cardinality estimates. -/
theorem card_taoLargePrimeExceptionalModuliPairs_cast_le
    (P : Fin 1001 → ℕ) (R S lowerPrime upperPrime : ℕ)
    (hR : taoDyadicPrimeBand R ⊆
      taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hS : taoDyadicPrimeBand S ⊆
      taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (A₁ A₂ B : ℝ)
    (hA₁ : (((taoDyadicPrimeBand R).filter fun p =>
      p ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card : ℝ) ≤ A₁)
    (hA₂ : (((taoDyadicPrimeBand S).filter fun q =>
      q ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card : ℝ) ≤ A₂)
    (hB : ∀ p ∈ taoDyadicPrimeBand R,
      (((taoDyadicPrimeBand S).filter fun q =>
        q ∈ taoLargePrimeExceptionalPartnersFor
          p lowerPrime upperPrime P).card : ℝ) ≤ B) :
    ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) ≤
      A₁ * ((taoDyadicPrimeBand S).card : ℝ) +
        ((taoDyadicPrimeBand R).card : ℝ) * A₂ +
        ((taoDyadicPrimeBand R).card : ℝ) * B := by
  have hcard := card_taoLargePrimeExceptionalModuliPairs_le
    P R S lowerPrime upperPrime hR hS
  have hcardReal : ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) ≤
      (((((taoDyadicPrimeBand R).filter fun p =>
          p ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card *
        (taoDyadicPrimeBand S).card) +
      ((taoDyadicPrimeBand R).card *
        ((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card) +
      ∑ p ∈ taoDyadicPrimeBand R,
        ((taoDyadicPrimeBand S).filter fun q =>
          q ∈ taoLargePrimeExceptionalPartnersFor
            p lowerPrime upperPrime P).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc
    ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) ≤ _ := hcardReal
    _ = (((taoDyadicPrimeBand R).filter fun p =>
          p ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card : ℝ) *
          ((taoDyadicPrimeBand S).card : ℝ) +
        ((taoDyadicPrimeBand R).card : ℝ) *
          (((taoDyadicPrimeBand S).filter fun q =>
            q ∈ taoLargePrimeExceptionalConductorsFor
              (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P).card : ℝ) +
        ∑ p ∈ taoDyadicPrimeBand R,
          (((taoDyadicPrimeBand S).filter fun q =>
            q ∈ taoLargePrimeExceptionalPartnersFor
              p lowerPrime upperPrime P).card : ℝ) := by
      push_cast
      rfl
    _ ≤ A₁ * ((taoDyadicPrimeBand S).card : ℝ) +
        ((taoDyadicPrimeBand R).card : ℝ) * A₂ +
        ∑ _p ∈ taoDyadicPrimeBand R, B := by
      gcongr
      exact hB _ ‹_›
    _ = A₁ * ((taoDyadicPrimeBand S).card : ℝ) +
        ((taoDyadicPrimeBand R).card : ℝ) * A₂ +
        ((taoDyadicPrimeBand R).card : ℝ) * B := by
      simp

end

end Tao2026
