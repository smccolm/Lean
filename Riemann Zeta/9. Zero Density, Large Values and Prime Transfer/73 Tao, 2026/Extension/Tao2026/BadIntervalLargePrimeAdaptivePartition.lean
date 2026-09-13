import Tao2026.BadIntervalLargePrimeAdaptiveError

/-!
# Adaptive prime-pair partition for the large-prime blocks

For an ordered pair of distinct prime moduli, the three primitive conductor
fibers have different natural adaptive scales.  The first-prime fiber uses
`R`, while the second-prime and product fibers use the partner scale `S`.
This module records that mixed partition exactly and connects it to the
adaptive prime and partner exceptional sets.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Mixed-scale unexceptionality for the three nontrivial conductors of an
ordered prime pair. -/
def TaoLargePrimeAdaptivePairUnexceptional
    (P : Fin 1001 → ℕ) (R S : ℕ) (a b : ℕ × ℕ) : Prop :=
  a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
      ((a.2 * b.2).divisors.erase 1) P R ∧
    b.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
      ((a.2 * b.2).divisors.erase 1) P S ∧
    a.2 * b.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
      ((a.2 * b.2).divisors.erase 1) P S

private theorem not_mem_adaptiveExceptionalFor_of_not_mem
    {D E : Finset ℕ} {q R : ℕ} {P : Fin 1001 → ℕ}
    (hqD : q ∈ D)
    (hq : q ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    q ∉ taoLargePrimeAdaptiveExceptionalConductorsFor E P R := by
  intro hqEbad
  apply hq
  rw [taoLargePrimeAdaptiveExceptionalConductorsFor,
    Finset.mem_biUnion] at hqEbad ⊢
  rcases hqEbad with ⟨j, hj, hjbad⟩
  refine ⟨j, hj, ?_⟩
  simp only [taoLargePrimeAdaptiveExceptionalConductorsIn,
    Finset.mem_filter] at hjbad ⊢
  exact ⟨hqD, hjbad.2⟩

/-- Removing the first prime at scale `R`, the second prime at scale `S`,
and the second prime from the adaptive partner set removes exactly the three
mixed-scale conductor fibers. -/
theorem taoLargePrimeAdaptivePairUnexceptional_of_prime_and_partner
    {lowerPrime upperPrime R S : ℕ} (P : Fin 1001 → ℕ)
    (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpD : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hqD : b.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hpGood : a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P R)
    (hqGood : b.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P S)
    (hpqGood : b.2 ∉ taoLargePrimeAdaptiveExceptionalPartnersFor
      a.2 lowerPrime upperPrime P S) :
    TaoLargePrimeAdaptivePairUnexceptional P R S a b := by
  have hpDiv : a.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one]
  have hqDiv : b.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hq.ne_one]
  have hpqDiv : a.2 * b.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one, hq.ne_one]
  refine ⟨not_mem_adaptiveExceptionalFor_of_not_mem hpD hpGood,
    not_mem_adaptiveExceptionalFor_of_not_mem hqD hqGood, ?_⟩
  intro hpqBad
  apply hpqGood
  rw [taoLargePrimeAdaptiveExceptionalPartnersFor, Finset.mem_biUnion]
  rw [taoLargePrimeAdaptiveExceptionalConductorsFor,
    Finset.mem_biUnion] at hpqBad
  rcases hpqBad with ⟨j, hj, hjbad⟩
  refine ⟨j, hj, ?_⟩
  simp only [taoLargePrimeAdaptiveExceptionalCofactorsIn,
    Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_erase.mpr ⟨hpq.symm, hqD⟩
  · rw [taoLargePrimeAdaptiveExceptionalConductorsIn,
      Finset.mem_filter] at hjbad
    exact hjbad.2

/-- Contrapositive covering form for the mixed adaptive pair partition. -/
theorem adaptive_exceptional_pair_mem_prime_or_prime_or_partner
    {lowerPrime upperPrime R S : ℕ} (P : Fin 1001 → ℕ)
    (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpD : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hqD : b.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (hbad : ¬TaoLargePrimeAdaptivePairUnexceptional P R S a b) :
    a.2 ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P R ∨
      b.2 ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P S ∨
      b.2 ∈ taoLargePrimeAdaptiveExceptionalPartnersFor
        a.2 lowerPrime upperPrime P S := by
  by_contra h
  push Not at h
  exact hbad (taoLargePrimeAdaptivePairUnexceptional_of_prime_and_partner
    P a b hp hq hpq hpD hqD h.1 h.2.1 h.2.2)

/-! ## Mixed conductor moments -/

/-- The primitive counterpart moment for a product of two distinct primes,
with the `p` conductor at scale `R` and the `q,pq` conductors at scale `S`. -/
theorem taoPrimitiveCounterpartMomentSum_le_adaptive_prime_pair
    {p q Z R S : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpEmpty : taoLargePrimeAdaptiveExceptionalCharacters p Z R = ∅)
    (hqEmpty : taoLargePrimeAdaptiveExceptionalCharacters q Z S = ∅)
    (hpqEmpty : taoLargePrimeAdaptiveExceptionalCharacters (p * q) Z S = ∅) :
    taoPrimitiveCounterpartMomentSum (p * q) Z ≤
      (p.totient : ℝ) *
          taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) +
        ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
          taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
  letI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rw [taoPrimitiveCounterpartMomentSum_eq_sum_fixedConductors
    (p * q) Z (Nat.mul_pos hp.pos hq.pos)]
  rw [prime_pair_divisors_erase_one hp hq hpq]
  have hpNeMul : p ≠ p * q := by
    intro h
    have h' : p * 1 = p * q := by simpa using h
    have := Nat.eq_of_mul_eq_mul_left hp.pos h'
    exact hq.ne_one this.symm
  have hqNeMul : q ≠ p * q := by
    intro h
    have h' : q * 1 = q * p := by simpa [Nat.mul_comm] using h
    have := Nat.eq_of_mul_eq_mul_left hq.pos h'
    exact hp.ne_one this.symm
  have hqNot : q ∉ ({p * q} : Finset ℕ) := by simp [hqNeMul]
  have hpNot : p ∉ ({q, p * q} : Finset ℕ) := by simp [hpq, hpNeMul]
  calc
    (∑ d ∈ ({p, q, p * q} : Finset ℕ),
        taoFixedConductorPrimitiveMomentSum (p * q) d Z) ≤
      (p.totient : ℝ) *
          taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) +
        (q.totient : ℝ) *
          taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) +
        ((p * q).totient : ℝ) *
          taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
      rw [Finset.sum_insert hpNot, Finset.sum_insert hqNot,
        Finset.sum_singleton]
      have hpqOne : p * q ≠ 1 := by
        intro h
        exact hp.ne_one (Nat.eq_one_of_dvd_one ⟨q, h.symm⟩)
      have hpBound := taoFixedConductorPrimitiveMomentSum_le_adaptive
        (p * q) p Z R hp.pos hp.ne_one hpEmpty
      have hqBound := taoFixedConductorPrimitiveMomentSum_le_adaptive
        (p * q) q Z S hq.pos hq.ne_one hqEmpty
      have hpqBound := taoFixedConductorPrimitiveMomentSum_le_adaptive
        (p * q) (p * q) Z S (Nat.mul_pos hp.pos hq.pos)
          hpqOne hpqEmpty
      simpa only [add_assoc] using
        add_le_add hpBound (add_le_add hqBound hpqBound)
    _ = (p.totient : ℝ) *
          taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) +
        ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
          taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by ring

/-- Ambient product-character moment with mixed adaptive conductor scales
and the exact change-level collision correction. -/
theorem sum_nonprincipalPrimeProduct_pow_thousand_le_adaptive_prime_pair
    {p q Z R S : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpEmpty : taoLargePrimeAdaptiveExceptionalCharacters p Z R = ∅)
    (hqEmpty : taoLargePrimeAdaptiveExceptionalCharacters q Z S = ∅)
    (hpqEmpty : taoLargePrimeAdaptiveExceptionalCharacters (p * q) Z S = ∅) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        ((p.totient : ℝ) *
            taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) +
          ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
            taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) +
          ((p * q).totient : ℝ) *
            (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by
  let δ : ℝ :=
    (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)
  calc
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
        ∑ χ ∈ taoNonprincipalCharacters (p * q),
          (2 : ℝ) ^ 999 *
            (‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^
              (1000 : ℕ) + δ) := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact norm_taoNormalizedPrimeCharacterSum_pow_thousand_le_primitive_add_collision
        (Z := Z) hp hq χ
    _ = (2 : ℝ) ^ 999 *
        (taoPrimitiveCounterpartMomentSum (p * q) Z +
          ((taoNonprincipalCharacters (p * q)).card : ℝ) * δ) := by
      rw [← Finset.mul_sum]
      unfold taoPrimitiveCounterpartMomentSum
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (2 : ℝ) ^ 999 *
        ((p.totient : ℝ) *
            taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) +
          ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
            taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) +
          ((p * q).totient : ℝ) * δ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply add_le_add
      · exact taoPrimitiveCounterpartMomentSum_le_adaptive_prime_pair
          hp hq hpq hpEmpty hqEmpty hpqEmpty
      · apply mul_le_mul_of_nonneg_right _ (pow_nonneg
          (mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg _))) _)
        exact_mod_cast card_taoNonprincipalCharacters_le_totient
          (p * q) (Nat.mul_pos hp.pos hq.pos)
    _ = _ := by rfl

/-- Coordinate-summed mixed adaptive product moment supplied directly by the
adaptive pair-unexceptionality predicate. -/
theorem sum_nonprincipalPrimeProduct_coordinateMoments_le_adaptive_prime_pair
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (P : Fin 1001 → ℕ) (R S : ℕ)
    (hpair : TaoLargePrimeAdaptivePairUnexceptional P R S (0, p) (0, q)) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        ((p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R +
          ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
            taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P) := by
  have hpDiv : p ∈ (p * q).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one]
  have hqDiv : q ∈ (p * q).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hq.ne_one]
  have hpqDiv : p * q ∈ (p * q).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one, hq.ne_one]
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters (p * q),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (2 : ℝ) ^ 999 *
            ((p.totient : ℝ) *
                taoLargePrimeAdaptiveThreshold (P j) R ^ (1000 : ℕ) +
              ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
                taoLargePrimeAdaptiveThreshold (P j) S ^ (1000 : ℕ) +
              ((p * q).totient : ℝ) *
                (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                  (1000 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeProduct_pow_thousand_le_adaptive_prime_pair
        hp hq hpq
      · apply taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
          hpDiv
        intro hpBad
        apply hpair.1
        rw [taoLargePrimeAdaptiveExceptionalConductorsFor,
          Finset.mem_biUnion]
        exact ⟨j, hj, hpBad⟩
      · apply taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
          hqDiv
        intro hqBad
        apply hpair.2.1
        rw [taoLargePrimeAdaptiveExceptionalConductorsFor,
          Finset.mem_biUnion]
        exact ⟨j, hj, hqBad⟩
      · apply taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
          hpqDiv
        intro hpqBad
        apply hpair.2.2
        rw [taoLargePrimeAdaptiveExceptionalConductorsFor,
          Finset.mem_biUnion]
        exact ⟨j, hj, hpqBad⟩
    _ = (2 : ℝ) ^ 999 *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((p.totient : ℝ) *
              taoLargePrimeAdaptiveThreshold (P j) R ^ (1000 : ℕ) +
            ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
              taoLargePrimeAdaptiveThreshold (P j) S ^ (1000 : ℕ) +
            ((p * q).totient : ℝ) *
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                (1000 : ℕ)) := by
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ 999 *
        ((p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R +
          ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
            taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P) := by
      unfold taoLargePrimeAdaptiveMomentSum
      unfold taoPrimeTupleChangeLevelCollisionSum
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

/-- Mixed-scale adaptive joint error matching the exact `p,q,pq` conductor
partition. -/
def taoLargePrimeMixedAdaptiveJointImprovedError
    (P : Fin 1001 → ℕ) (p q R S : ℕ) : ℝ :=
  ((p * q).totient : ℝ)⁻¹ *
    (2 * taoPrimeTupleBandReciprocalSum P +
      (2 : ℝ) ^ 999 *
        ((p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R +
          ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
            taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P))

theorem taoLargePrimeMixedAdaptiveJointImprovedError_nonneg
    (P : Fin 1001 → ℕ) (p q R S : ℕ) :
    0 ≤ taoLargePrimeMixedAdaptiveJointImprovedError P p q R S := by
  unfold taoLargePrimeMixedAdaptiveJointImprovedError
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply add_nonneg
  · exact mul_nonneg (by norm_num)
      (taoPrimeTupleBandReciprocalSum_nonneg P)
  · apply mul_nonneg (pow_nonneg (by norm_num) _)
    exact add_nonneg (add_nonneg
      (mul_nonneg (by positivity)
        (taoLargePrimeAdaptiveMomentSum_nonneg P R))
      (mul_nonneg (add_nonneg (by positivity) (by positivity))
        (taoLargePrimeAdaptiveMomentSum_nonneg P S)))
      (mul_nonneg (by positivity)
        (taoPrimeTupleChangeLevelCollisionSum_nonneg P))

/-- Mixed adaptive product-modulus residue-fiber deviation. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_mixedAdaptive
    {p q a m' R S : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (ha : Nat.Coprime a (p * q))
    (hm : Nat.Coprime m' (p * q))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpair : TaoLargePrimeAdaptivePairUnexceptional P R S (0, p) (0, q)) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        (2 * taoPrimeTupleBandReciprocalSum P +
          (2 : ℝ) ^ 999 *
            ((p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R +
              ((q.totient : ℝ) + ((p * q).totient : ℝ)) *
                taoLargePrimeAdaptiveMomentSum P S +
              ((p * q).totient : ℝ) *
                taoPrimeTupleChangeLevelCollisionSum P)) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime_mul
    hp hq ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment :=
    sum_nonprincipalPrimeProduct_coordinateMoments_le_adaptive_prime_pair
      hp hq hpq P R S hpair
  unfold taoPrimeTupleBandReciprocalSum taoPrimeTupleChangeLevelCollisionSum
  exact add_le_add le_rfl hMoment

/-- Literal joint probability bound for a mixed-scale adaptively
unexceptional pair. -/
theorem taoLargePrimeJointProbability_le_main_add_mixedAdaptiveError
    {m' R S : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpair : TaoLargePrimeAdaptivePairUnexceptional P R S a b) :
    taoLargePrimeJointProbability P hP m' a b ≤
      1 / ((a.2 * b.2).totient : ℝ) +
        taoLargePrimeMixedAdaptiveJointImprovedError P a.2 b.2 R S := by
  have hpairZero :
      TaoLargePrimeAdaptivePairUnexceptional P R S (0, a.2) (0, b.2) := by
    simpa only [TaoLargePrimeAdaptivePairUnexceptional] using hpair
  rcases taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    hp hq hpq hpa hqb with hempty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeJointProbability, hempty, MeasureTheory.measureReal_empty]
    exact add_nonneg (by positivity)
      (taoLargePrimeMixedAdaptiveJointImprovedError_nonneg
        P a.2 b.2 R S)
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_mixedAdaptive
        hp hq hpq hr hm P hP hpairZero
    rw [taoLargePrimeJointProbability, hset]
    have hreal :
        |(taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
            1 / ((a.2 * b.2).totient : ℝ)| ≤
          taoLargePrimeMixedAdaptiveJointImprovedError
            P a.2 b.2 R S := by
      have heq :
          (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} : ℝ) : ℂ) -
              (1 / ((a.2 * b.2).totient : ℂ)) =
            (((taoPrimeTupleMeasure P hP).real
                {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
              1 / ((a.2 * b.2).totient : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real] at hnorm
      simpa [taoLargePrimeMixedAdaptiveJointImprovedError, one_div] using hnorm
    nlinarith [le_trans (le_abs_self
      ((taoPrimeTupleMeasure P hP).real
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
        1 / ((a.2 * b.2).totient : ℝ))) hreal]

/-! ## Mixed source-power normalization -/

private theorem mixed_adaptive_tail_le_ordered_power
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hRS : R ≤ S) :
    (S : ℝ) ^ (-(10 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := by
  have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
  have hSpos : 0 < S := Nat.zero_lt_one.trans_le hS
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hSpos
  have hNine : (S : ℝ) ^ (-(9 : ℝ)) ≤
      (S : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hS) (by norm_num)
  have hCross : (S : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hRpos)
      (by exact_mod_cast hRS) (by norm_num)
  rw [show (-(10 : ℝ)) = -(9 : ℝ) + -(1 : ℝ) by ring,
    Real.rpow_add hSreal]
  exact mul_le_mul_of_nonneg_right (hNine.trans hCross) (by positivity)

/-- The exact mixed adaptive joint error is controlled by three copies of
the fixed error plus one explicit ordered-band adaptive tail. -/
theorem taoLargePrimeMixedAdaptiveJointImprovedError_le_three_mul_fixed_add
    (P : Fin 1001 → ℕ) {p q R S : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hR : 2 ≤ R) (hS : 2 ≤ S) (hRS : R ≤ S)
    (hqS : q ∈ taoDyadicPrimeBand S) :
    taoLargePrimeMixedAdaptiveJointImprovedError P p q R S ≤
      3 * taoLargePrimeJointImprovedError P p q +
        (2 : ℝ) ^ 999 * 4000 *
          ((R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
            (S : ℝ) ^ (-(1 : ℝ))) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have htotient : (p * q).totient = p.totient * q.totient :=
    Nat.totient_mul hcop
  have hφp : (0 : ℝ) < (p.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hφq : (0 : ℝ) < (q.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hq.pos
  have hφpq : (0 : ℝ) < ((p * q).totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hp.pos hq.pos)
  let A : ℝ := ((p * q).totient : ℝ)⁻¹ *
    (2 * taoPrimeTupleBandReciprocalSum P)
  let c : ℝ := (2 : ℝ) ^ 999
  let α : ℝ := (p.totient : ℝ) / ((p * q).totient : ℝ)
  let β : ℝ := ((q.totient : ℝ) + ((p * q).totient : ℝ)) /
    ((p * q).totient : ℝ)
  let ρ : ℝ := ((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ)
  let V : ℝ := taoPrimeTupleEighthPowerSum P
  let MR : ℝ := taoLargePrimeAdaptiveMomentSum P R
  let MS : ℝ := taoLargePrimeAdaptiveMomentSum P S
  let W : ℝ := taoPrimeTupleChangeLevelCollisionSum P
  let tR : ℝ := (R : ℝ) ^ (-(10 : ℝ))
  let tS : ℝ := (S : ℝ) ^ (-(10 : ℝ))
  let T : ℝ := (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
    (S : ℝ) ^ (-(1 : ℝ))
  have hMixed :
      taoLargePrimeMixedAdaptiveJointImprovedError P p q R S =
        A + c * (α * MR + β * MS + W) := by
    dsimp [A, c, α, β, MR, MS, W]
    rw [taoLargePrimeMixedAdaptiveJointImprovedError]
    field_simp
  have hFixed :
      taoLargePrimeJointImprovedError P p q =
        A + c * (ρ * V + W) := by
    dsimp [A, c, ρ, V, W]
    rw [taoLargePrimeJointImprovedError]
    change ((p * q).totient : ℝ)⁻¹ *
        (2 * taoPrimeTupleBandReciprocalSum P +
          (2 : ℝ) ^ 999 *
            (((p * q : ℕ) : ℝ) * taoPrimeTupleEighthPowerSum P +
              ((p * q).totient : ℝ) *
                taoPrimeTupleChangeLevelCollisionSum P)) = _
    field_simp
  have hαEq : α = 1 / (q.totient : ℝ) := by
    dsimp [α]
    rw [htotient]
    push_cast
    field_simp
  have hβEq : β = 1 / (p.totient : ℝ) + 1 := by
    dsimp [β]
    rw [htotient]
    push_cast
    field_simp
  have hαNonneg : 0 ≤ α := by dsimp [α]; positivity
  have hβNonneg : 0 ≤ β := by dsimp [β]; positivity
  have hαOne : α ≤ 1 := by
    rw [hαEq]
    have hOne : (1 : ℝ) ≤ (q.totient : ℕ) := by
      exact_mod_cast Nat.totient_pos.mpr hq.pos
    apply (div_le_iff₀ hφq).2
    simpa only [one_mul] using hOne
  have hβTwo : β ≤ 2 := by
    rw [hβEq]
    have hInv : 1 / (p.totient : ℝ) ≤ 1 := by
      have hOne : (1 : ℝ) ≤ (p.totient : ℕ) := by
        exact_mod_cast Nat.totient_pos.mpr hp.pos
      apply (div_le_iff₀ hφp).2
      simpa only [one_mul] using hOne
    linarith
  have hαBand : α ≤ 2 / (S : ℝ) := by
    rw [hαEq]
    exact one_div_totient_le_two_div_dyadicStart hS hq
      (mem_taoDyadicPrimeBand.mp hqS).2.1
  have hρOne : 1 ≤ ρ := by
    dsimp [ρ]
    apply (le_div_iff₀ hφpq).2
    simpa only [one_mul] using
      (show (((p * q).totient : ℕ) : ℝ) ≤ (p * q : ℕ) by
        exact_mod_cast Nat.totient_le (p * q))
  have hVNonneg : 0 ≤ V := by
    exact taoPrimeTupleEighthPowerSum_nonneg P
  have hWNonneg : 0 ≤ W := by
    exact taoPrimeTupleChangeLevelCollisionSum_nonneg P
  have htRNonneg : 0 ≤ tR := by dsimp [tR]; positivity
  have htSNonneg : 0 ≤ tS := by dsimp [tS]; positivity
  have hMR : MR ≤ V + 1000 * tR :=
    taoLargePrimeAdaptiveMomentSum_le P R
  have hMS : MS ≤ V + 1000 * tS :=
    taoLargePrimeAdaptiveMomentSum_le P S
  have hMoment : α * MR + β * MS ≤
      3 * V + α * (1000 * tR) + β * (1000 * tS) := by
    calc
      α * MR + β * MS ≤
          α * (V + 1000 * tR) + β * (V + 1000 * tS) :=
        add_le_add (mul_le_mul_of_nonneg_left hMR hαNonneg)
          (mul_le_mul_of_nonneg_left hMS hβNonneg)
      _ = (α + β) * V + α * (1000 * tR) + β * (1000 * tS) := by ring
      _ ≤ 3 * V + α * (1000 * tR) + β * (1000 * tS) := by
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right
            (by linarith [hαOne, hβTwo]) hVNonneg) le_rfl) le_rfl
  have hRt : tR ≤ (R : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
    dsimp [tR]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ R by omega)) (by norm_num)
  have hSt : tS ≤ T := by
    exact mixed_adaptive_tail_le_ordered_power
      (show 1 ≤ R by omega) (show 1 ≤ S by omega) hRS
  have hAlphaTail : α * (1000 * tR) ≤ 2000 * T := by
    calc
      α * (1000 * tR) ≤ (2 / (S : ℝ)) * (1000 * tR) :=
        mul_le_mul_of_nonneg_right hαBand (mul_nonneg (by norm_num) htRNonneg)
      _ = 2000 * (tR * (S : ℝ) ^ (-(1 : ℝ))) := by
        have hSreal : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        ring
      _ ≤ 2000 * T := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hRt (by positivity)
  have hBetaTail : β * (1000 * tS) ≤ 2000 * T := by
    calc
      β * (1000 * tS) ≤ 2 * (1000 * tS) :=
        mul_le_mul_of_nonneg_right hβTwo (mul_nonneg (by norm_num) htSNonneg)
      _ = 2000 * tS := by ring
      _ ≤ 2000 * T := mul_le_mul_of_nonneg_left hSt (by norm_num)
  have hMomentT : α * MR + β * MS ≤ 3 * V + 4000 * T := by
    calc
      α * MR + β * MS ≤
          3 * V + α * (1000 * tR) + β * (1000 * tS) := hMoment
      _ ≤ 3 * V + 2000 * T + 2000 * T :=
        add_le_add (add_le_add le_rfl hAlphaTail) hBetaTail
      _ = 3 * V + 4000 * T := by ring
  have hBase : α * MR + β * MS + W ≤
      3 * (ρ * V + W) + 4000 * T := by
    have hρV : V ≤ ρ * V := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hρOne hVNonneg
    calc
      α * MR + β * MS + W ≤ (3 * V + 4000 * T) + W :=
        add_le_add hMomentT le_rfl
      _ ≤ 3 * (ρ * V + W) + 4000 * T := by
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hWNonneg,
          mul_le_mul_of_nonneg_left hρV (by norm_num : (0 : ℝ) ≤ 3)]
  have hANonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (mul_nonneg (by norm_num) (taoPrimeTupleBandReciprocalSum_nonneg P))
  have hcNonneg : 0 ≤ c := pow_nonneg (by norm_num) 999
  rw [hMixed, hFixed]
  calc
    A + c * (α * MR + β * MS + W) ≤
        A + c * (3 * (ρ * V + W) + 4000 * T) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hBase hcNonneg)
    _ ≤ 3 * (A + c * (ρ * V + W)) + c * 4000 * T := by
      have hA : A ≤ 3 * A := by nlinarith
      have hInner : A + 3 * (c * (ρ * V + W)) ≤
          3 * (A + c * (ρ * V + W)) := by
        calc
          A + 3 * (c * (ρ * V + W)) ≤
              3 * A + 3 * (c * (ρ * V + W)) := add_le_add hA le_rfl
          _ = 3 * (A + c * (ρ * V + W)) :=
            (mul_add 3 A (c * (ρ * V + W))).symm
      calc
        A + c * (3 * (ρ * V + W) + 4000 * T) =
            (A + 3 * (c * (ρ * V + W))) + c * 4000 * T := by
          have hFirst : c * (3 * (ρ * V + W)) =
              3 * (c * (ρ * V + W)) := by ac_rfl
          have hSecond : c * (4000 * T) = c * 4000 * T := by
            rw [mul_assoc]
          rw [mul_add c (3 * (ρ * V + W)) (4000 * T), hFirst, hSecond,
            ← add_assoc]
        _ ≤ 3 * (A + c * (ρ * V + W)) + c * 4000 * T :=
          add_le_add hInner le_rfl
    _ = 3 * (A + c * (ρ * V + W)) +
        (2 : ℝ) ^ 999 * 4000 *
          ((R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
            (S : ℝ) ^ (-(1 : ℝ))) := by rfl

/-- Explicit constant for the exact mixed adaptive joint error. -/
def taoLargePrimeMixedAdaptiveSourceJointPowerConstant : ℝ :=
  3 * taoLargePrimeSourceJointPowerConstant + (2 : ℝ) ^ 999 * 4000

/-- The exact mixed adaptive joint error has the ordered source power
`O(R^-1.001 S^-1)`. -/
theorem eventually_taoLargePrimeMixedAdaptiveJointImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in Filter.atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeMixedAdaptiveJointImprovedError
          (P x) p q (R x) (S x) ≤
        taoLargePrimeMixedAdaptiveSourceJointPowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [eventually_taoLargePrimeJointImprovedError_le_sourcePower
      hscale hR hS, hR.eventually_two_le, hS.eventually_two_le, hRS] with
      x hFixed hRtwo hStwo hRSx
  intro p q hp hq hpq
  let T : ℝ := (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
    (S x : ℝ) ^ (-(1 : ℝ))
  have hFixedT : taoLargePrimeJointImprovedError (P x) p q ≤
      taoLargePrimeSourceJointPowerConstant * T := by
    dsimp only [T]
    rw [← mul_assoc]
    exact hFixed p q hp hq hpq
  calc
    taoLargePrimeMixedAdaptiveJointImprovedError
        (P x) p q (R x) (S x) ≤
      3 * taoLargePrimeJointImprovedError (P x) p q +
        (2 : ℝ) ^ 999 * 4000 * T := by
      exact taoLargePrimeMixedAdaptiveJointImprovedError_le_three_mul_fixed_add
        (P x) (mem_taoDyadicPrimeBand.mp hp).1
          (mem_taoDyadicPrimeBand.mp hq).1 hpq hRtwo hStwo hRSx hq
    _ ≤ 3 * (taoLargePrimeSourceJointPowerConstant * T) +
        (2 : ℝ) ^ 999 * 4000 * T :=
      add_le_add (mul_le_mul_of_nonneg_left hFixedT (by norm_num)) le_rfl
    _ = taoLargePrimeMixedAdaptiveSourceJointPowerConstant *
        (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S x : ℝ) ^ (-(1 : ℝ)) := by
      rw [taoLargePrimeMixedAdaptiveSourceJointPowerConstant]
      rw [mul_assoc
        (3 * taoLargePrimeSourceJointPowerConstant + (2 : ℝ) ^ 999 * 4000)
        ((R x : ℝ) ^ (-(1001 / 1000 : ℝ)))
        ((S x : ℝ) ^ (-(1 : ℝ))), add_mul]
      dsimp only [T]
      rw [mul_assoc 3 taoLargePrimeSourceJointPowerConstant,
        mul_assoc ((2 : ℝ) ^ 999) 4000]

/-! ## Mixed adaptive covariance errors -/

/-- Complete covariance error for the exact mixed `p,q,pq` adaptive
partition. -/
def taoLargePrimeMixedAdaptiveCovarianceImprovedError
    (P : Fin 1001 → ℕ) (p q R S : ℕ) : ℝ :=
  taoLargePrimeMixedAdaptiveJointImprovedError P p q R S +
    (1 / (p.totient : ℝ)) * taoLargePrimeAdaptiveImprovedError P q S +
    (1 / (q.totient : ℝ)) * taoLargePrimeAdaptiveImprovedError P p R +
    taoLargePrimeAdaptiveImprovedError P p R *
      taoLargePrimeAdaptiveImprovedError P q S

/-- Covariance estimate outside the exact mixed adaptive pair partition. -/
theorem taoLargePrimeCovariance_le_mixedAdaptiveErrors
    {m' R S : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpair : TaoLargePrimeAdaptivePairUnexceptional P R S a b) :
    taoLargePrimeCovariance P hP m' a b ≤
      taoLargePrimeMixedAdaptiveCovarianceImprovedError
        P a.2 b.2 R S := by
  have hmParts : Nat.Coprime m' a.2 ∧ Nat.Coprime m' b.2 :=
    Nat.coprime_mul_iff_right.mp hm
  have hpqCoprime : Nat.Coprime a.2 b.2 :=
    (Nat.coprime_primes hp hq).2 hpq
  have htotient : (a.2 * b.2).totient =
      a.2.totient * b.2.totient := Nat.totient_mul hpqCoprime
  have hmain :
      1 / ((a.2 * b.2).totient : ℝ) =
        (1 / (a.2.totient : ℝ)) *
          (1 / (b.2.totient : ℝ)) := by
    rw [htotient]
    push_cast
    simp only [one_div, mul_inv]
  have hpDiv : a.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hp.ne_one]
  have hqDiv : b.2 ∈ (a.2 * b.2).divisors.erase 1 := by
    simp [Nat.mem_divisors, hp.ne_zero, hq.ne_zero, hq.ne_one]
  have hJ := taoLargePrimeJointProbability_le_main_add_mixedAdaptiveError
    a b hp hq hpq hpa hqb hm P hP hpair
  rw [hmain] at hJ
  have ha := abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    a hp hpDiv hpa hmParts.1 P hP hpair.1
  have hb := abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    b hq hqDiv hqb hmParts.2 P hP hpair.2.1
  rw [taoLargePrimeCovariance]
  unfold taoLargePrimeMixedAdaptiveCovarianceImprovedError
  exact sub_mul_le_of_abs_sub_le hJ ha hb
    (by positivity) (by positivity)
      (taoLargePrimeAdaptiveImprovedError_nonneg P a.2 R)

/-- Explicit constant for the exact mixed adaptive covariance source-power
error. -/
def taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant : ℝ :=
  taoLargePrimeMixedAdaptiveSourceJointPowerConstant + 1010021

private theorem mixed_adaptive_selector_cross_power_le
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) :
    (R : ℝ) ^ (-(1 : ℝ)) *
        (S : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hRSreal : (R : ℝ) ≤ S := by exact_mod_cast hRS
  have hdelta : (S : ℝ) ^ (-(1 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hRreal hRSreal (by norm_num)
  have hRsplit : (R : ℝ) ^ (-(1001 / 1000 : ℝ)) =
      (R : ℝ) ^ (-(1 : ℝ)) *
        (R : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hRreal]
    congr 1
    norm_num
  have hSsplit : (S : ℝ) ^ (-(1001 / 1000 : ℝ)) =
      (S : ℝ) ^ (-(1 : ℝ)) *
        (S : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hSreal]
    congr 1
    norm_num
  rw [hRsplit, hSsplit]
  calc
    (R : ℝ) ^ (-(1 : ℝ)) *
        ((S : ℝ) ^ (-(1 : ℝ)) *
          (S : ℝ) ^ (-(1 / 1000 : ℝ))) =
      ((R : ℝ) ^ (-(1 : ℝ)) * (S : ℝ) ^ (-(1 : ℝ))) *
        (S : ℝ) ^ (-(1 / 1000 : ℝ)) := by ring
    _ ≤ ((R : ℝ) ^ (-(1 : ℝ)) * (S : ℝ) ^ (-(1 : ℝ))) *
        (R : ℝ) ^ (-(1 / 1000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdelta (by positivity)
    _ = ((R : ℝ) ^ (-(1 : ℝ)) *
          (R : ℝ) ^ (-(1 / 1000 : ℝ))) *
        (S : ℝ) ^ (-(1 : ℝ)) := by ring

/-- The exact mixed adaptive covariance error has ordered source power
`O(R^-1.001 S^-1)`. -/
theorem eventually_taoLargePrimeMixedAdaptiveCovarianceImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in Filter.atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeMixedAdaptiveCovarianceImprovedError
          (P x) p q (R x) (S x) ≤
        taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeMixedAdaptiveJointImprovedError_le_sourcePower
      hscale hR hS hRS,
    eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower hscale hR,
    eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower hscale hS,
    hR.eventually_two_le, hS.eventually_two_le, hRS] with
      x hJoint hSingleR hSingleS hRtwo hStwo hRSx
  intro p q hp hq hpq
  let A : ℝ := (R x : ℝ) ^ (-(1001 / 1000 : ℝ))
  let B : ℝ := (S x : ℝ) ^ (-(1 : ℝ))
  let T : ℝ := A * B
  let ER : ℝ := taoLargePrimeAdaptiveImprovedError (P x) p (R x)
  let ES : ℝ := taoLargePrimeAdaptiveImprovedError (P x) q (S x)
  have hpPrime : Nat.Prime p := (mem_taoDyadicPrimeBand.mp hp).1
  have hqPrime : Nat.Prime q := (mem_taoDyadicPrimeBand.mp hq).1
  have hφp : 1 / (p.totient : ℝ) ≤ 2 / (R x : ℝ) :=
    one_div_totient_le_two_div_dyadicStart hRtwo hpPrime
      (mem_taoDyadicPrimeBand.mp hp).2.1
  have hφq : 1 / (q.totient : ℝ) ≤ 2 / (S x : ℝ) :=
    one_div_totient_le_two_div_dyadicStart hStwo hqPrime
      (mem_taoDyadicPrimeBand.mp hq).2.1
  have hER : ER ≤ 1003 * A := hSingleR p hp
  have hES : ES ≤
      1003 * (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) := hSingleS q hq
  have hJointT :
      taoLargePrimeMixedAdaptiveJointImprovedError
          (P x) p q (R x) (S x) ≤
        taoLargePrimeMixedAdaptiveSourceJointPowerConstant * T := by
    dsimp only [T, A, B]
    rw [← mul_assoc]
    exact hJoint p q hp hq hpq
  have hERnonneg : 0 ≤ ER :=
    taoLargePrimeAdaptiveImprovedError_nonneg (P x) p (R x)
  have hESnonneg : 0 ≤ ES :=
    taoLargePrimeAdaptiveImprovedError_nonneg (P x) q (S x)
  have hCross : (R x : ℝ) ^ (-(1 : ℝ)) *
      (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤ T := by
    exact mixed_adaptive_selector_cross_power_le (by omega) (by omega) hRSx
  have hSdecay : (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤ B := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ S x by omega)) (by norm_num)
  have hMarginalS :
      (1 / (p.totient : ℝ)) * ES ≤ 2006 * T := by
    calc
      (1 / (p.totient : ℝ)) * ES ≤
          (2 / (R x : ℝ)) *
            (1003 * (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) :=
        mul_le_mul hφp hES hESnonneg (by positivity)
      _ = 2006 * ((R x : ℝ) ^ (-(1 : ℝ)) *
          (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) := by
        have hRx : (0 : ℝ) < R x := by exact_mod_cast (show 0 < R x by omega)
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        ring
      _ ≤ 2006 * T := mul_le_mul_of_nonneg_left hCross (by norm_num)
  have hMarginalR :
      (1 / (q.totient : ℝ)) * ER ≤ 2006 * T := by
    calc
      (1 / (q.totient : ℝ)) * ER ≤
          (2 / (S x : ℝ)) * (1003 * A) :=
        mul_le_mul hφq hER hERnonneg (by positivity)
      _ = 2006 * T := by
        have hSx : (0 : ℝ) < S x := by exact_mod_cast (show 0 < S x by omega)
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        dsimp only [T, B]
        ring
  have hProduct : ER * ES ≤ 1006009 * T := by
    calc
      ER * ES ≤ (1003 * A) *
          (1003 * (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) :=
        mul_le_mul hER hES hESnonneg (by positivity)
      _ = 1006009 *
          (A * (S x : ℝ) ^ (-(1001 / 1000 : ℝ))) := by ring
      _ ≤ 1006009 * (A * B) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSdecay (by dsimp [A]; positivity))
          (by norm_num)
      _ = 1006009 * T := by rfl
  have hcombine (c t : ℝ) :
      c * t + 2006 * t + 2006 * t + 1006009 * t =
        (c + 1010021) * t := by ring
  unfold taoLargePrimeMixedAdaptiveCovarianceImprovedError
  calc
    taoLargePrimeMixedAdaptiveJointImprovedError
          (P x) p q (R x) (S x) +
          (1 / (p.totient : ℝ)) * ES +
          (1 / (q.totient : ℝ)) * ER + ER * ES ≤
        taoLargePrimeMixedAdaptiveSourceJointPowerConstant * T +
          2006 * T + 2006 * T + 1006009 * T := by
      exact add_le_add (add_le_add (add_le_add
        hJointT hMarginalS) hMarginalR) hProduct
    _ = taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant *
        (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S x : ℝ) ^ (-(1 : ℝ)) := by
      rw [hcombine]
      rw [taoLargePrimeMixedAdaptiveSourceCovariancePowerConstant]
      dsimp only [T, A, B]
      rw [← mul_assoc]

end

end Tao2026
