import Tao2026.BadIntervalLargePrimeProductNonprincipal

/-!
# Product-modulus change-level collision removal

This module removes the coprime-band representation restriction from the
two-prime nonprincipal estimate.  An ambient character modulo `p*q` and its
primitive counterpart agree away from the at most two band points `p,q`.
Their normalized averages therefore differ by at most four reciprocal band
cardinalities.  A 1000th-power convexity estimate propagates this correction,
while a coprimality-free conductor regrouping controls all primitive
counterparts.  The final theorem gives the direct Proposition 6.8 deviation
bound with an explicit collision correction and no band-separation hypothesis.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- The primes in the scale-`Z` band that are not coprime to `p*q`. -/
def taoPrimeProductNoncoprimeBand (p q Z : ℕ) : Finset ℕ :=
  (taoDyadicPrimeBand Z).filter fun r => ¬ Nat.Coprime r (p * q)

theorem taoPrimeProductNoncoprimeBand_subset
    {p q Z : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    taoPrimeProductNoncoprimeBand p q Z ⊆ {p, q} := by
  intro r hr
  have hrData := Finset.mem_filter.mp hr
  have hrPrime : Nat.Prime r := (mem_taoDyadicPrimeBand.mp hrData.1).1
  have hdiv : r ∣ p * q := by
    by_contra hnot
    exact hrData.2 (hrPrime.coprime_iff_not_dvd.mpr hnot)
  rcases (hrPrime.dvd_mul.mp hdiv) with hrp | hrq
  · have : r = p := (Nat.prime_dvd_prime_iff_eq hrPrime hp).mp hrp
    simp [this]
  · have : r = q := (Nat.prime_dvd_prime_iff_eq hrPrime hq).mp hrq
    simp [this]

theorem card_taoPrimeProductNoncoprimeBand_le_two
    {p q Z : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (taoPrimeProductNoncoprimeBand p q Z).card ≤ 2 := by
  calc
    (taoPrimeProductNoncoprimeBand p q Z).card ≤
        ({p, q} : Finset ℕ).card :=
      Finset.card_le_card (taoPrimeProductNoncoprimeBand_subset hp hq)
    _ ≤ 2 := by
      exact (Finset.card_insert_le p {q}).trans (by simp)

/-- Changing an ambient character modulo `p*q` to its primitive conductor can
alter the normalized prime average only at the at most two modulus primes.
The factor four comes from a norm-two pointwise difference. -/
theorem norm_taoNormalizedPrimeCharacterSum_sub_primitiveCharacter_le_prime_mul
    {p q Z : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (χ : DirichletCharacter ℂ (p * q)) :
    ‖taoNormalizedPrimeCharacterSum χ Z -
        taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ≤
      4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹ := by
  let B := taoDyadicPrimeBand Z
  let E := taoPrimeProductNoncoprimeBand p q Z
  let f : ℕ → ℂ := fun r =>
    χ (r : ZMod (p * q)) - χ.primitiveCharacter (r : ZMod χ.conductor)
  have hsum : (∑ r ∈ B, f r) = ∑ r ∈ E, f r := by
    rw [show E = B.filter (fun r => ¬ Nat.Coprime r (p * q)) by rfl]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hc : Nat.Coprime r (p * q)
    · rw [if_neg (not_not.mpr hc)]
      change χ (r : ZMod (p * q)) -
        χ.primitiveCharacter (r : ZMod χ.conductor) = 0
      have heq := changeLevel_apply_natCast_of_coprime
        χ.primitiveCharacter χ.conductor_dvd_level hc
      rw [show χ (r : ZMod (p * q)) =
          (DirichletCharacter.changeLevel χ.conductor_dvd_level
            χ.primitiveCharacter) (r : ZMod (p * q)) by
        exact congrArg (fun ψ : DirichletCharacter ℂ (p * q) =>
          ψ (r : ZMod (p * q))) χ.changeLevel_primitiveCharacter.symm]
      simp [heq]
    · rw [if_pos hc]
  have hsumNorm : ‖∑ r ∈ E, f r‖ ≤ 4 := by
    calc
      ‖∑ r ∈ E, f r‖ ≤ ∑ r ∈ E, ‖f r‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ E, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (norm_sub_le _ _).trans (by
          have hχ := DirichletCharacter.norm_le_one χ (r : ZMod (p * q))
          have hψ := DirichletCharacter.norm_le_one χ.primitiveCharacter
            (r : ZMod χ.conductor)
          linarith)
      _ = 2 * E.card := by simp [mul_comm]
      _ ≤ 4 := by
        have hcard : E.card ≤ 2 :=
          card_taoPrimeProductNoncoprimeBand_le_two hp hq
        have hcardReal : (E.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        nlinarith
  unfold taoNormalizedPrimeCharacterSum taoDyadicPrimeCharacterAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  change ‖((B.card : ℂ)⁻¹ * ∑ r ∈ B, f r)‖ ≤ _
  rw [hsum, norm_mul]
  calc
    ‖(B.card : ℂ)⁻¹‖ * ‖∑ r ∈ E, f r‖ ≤
        ‖(B.card : ℂ)⁻¹‖ * 4 := by
      exact mul_le_mul_of_nonneg_left hsumNorm (norm_nonneg _)
    _ = 4 * (B.card : ℝ)⁻¹ := by
      simp [mul_comm]

/-- Pure conductor regrouping of primitive counterparts.  Unlike the ambient
moment equality, this statement requires no coprimality of the prime band with
the ambient modulus. -/
theorem taoPrimitiveCounterpartMomentSum_eq_sum_fixedConductors
    (q Z : ℕ) (hq : 0 < q) :
    taoPrimitiveCounterpartMomentSum q Z =
      ∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z := by
  letI : NeZero q := ⟨hq.ne'⟩
  let f : DirichletCharacter ℂ q → ℝ := fun χ =>
    ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ)
  have hMaps : ∀ χ ∈ taoNonprincipalCharacters q,
      χ.conductor ∈ q.divisors.erase 1 := by
    intro χ hχ
    rw [Finset.mem_erase, Nat.mem_divisors]
    have hNonprincipal : χ ≠ 1 := mem_taoNonprincipalCharacters.mp hχ
    have hConductorOne : χ.conductor ≠ 1 := by
      intro hOne
      exact hNonprincipal
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hOne)
    exact ⟨hConductorOne, χ.conductor_dvd_level, hq.ne'⟩
  have hFiber := Finset.sum_fiberwise_of_maps_to hMaps f
  unfold taoPrimitiveCounterpartMomentSum
  calc
    (∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ)) =
        ∑ d ∈ q.divisors.erase 1,
          ∑ χ ∈ taoNonprincipalCharacters q with χ.conductor = d,
            f χ := by
      simpa only [f] using hFiber.symm
    _ = ∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← taoCharactersOfConductor_eq_filter_nonprincipal q d
        (Finset.ne_of_mem_erase hd)]
      unfold taoFixedConductorPrimitiveMomentSum
      rw [← Finset.sum_attach (taoCharactersOfConductor q d)
        (fun χ => ‖taoNormalizedPrimeCharacterSum
          χ.primitiveCharacter Z‖ ^ (1000 : ℕ))]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [taoNormalizedPrimeCharacterSum_primitiveConductorElement]

theorem card_taoNonprincipalCharacters_le_totient (q : ℕ) (hq : 0 < q) :
    (taoNonprincipalCharacters q).card ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (taoNonprincipalCharacters q).card ≤
        Fintype.card (DirichletCharacter ℂ q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card fun χ _ => Finset.mem_univ χ
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- Coprimality-free primitive-counterpart moment bound when every nontrivial
divisor conductor is unexceptional. -/
theorem taoPrimitiveCounterpartMomentSum_le_unexceptional_divisors
    {q Z : ℕ} (hq : 0 < q) (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hExceptional : ∀ d ∈ q.divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsIn (q.divisors.erase 1) Z) :
    taoPrimitiveCounterpartMomentSum q Z ≤
      (q : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [taoPrimitiveCounterpartMomentSum_eq_sum_fixedConductors q Z hq]
  calc
    (∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z) ≤
        ∑ d ∈ q.divisors.erase 1,
          (d.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdMem : d ∈ q.divisors := Finset.mem_of_mem_erase hd
      have hdDvd : d ∣ q := (Nat.mem_divisors.mp hdMem).1
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDvd hq
      have hEmpty : taoExceptionalPrimitiveCharacters d Z = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hNonempty
        apply hExceptional d hd
        simp [taoLargePrimeExceptionalConductorsIn, hd, hNonempty]
      simpa [hEmpty] using
        (taoFixedConductorPrimitiveMomentSum_le_exceptional_sq_add
          q d Z hdPos (Finset.ne_of_mem_erase hd) hZ)
    _ = ((∑ d ∈ q.divisors.erase 1, d.totient : ℕ) : ℝ) *
        (Z : ℝ) ^ (-(8 : ℝ)) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (q : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
      exact_mod_cast sum_totient_divisors_erase_one_le q

/-- Convexity transfers the two-point change-level error through the source's
1000th power. -/
theorem norm_taoNormalizedPrimeCharacterSum_pow_thousand_le_primitive_add_collision
    {p q Z : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (χ : DirichletCharacter ℂ (p * q)) :
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) ≤
      (2 : ℝ) ^ 999 *
        (‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ) +
          (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by
  have hdiff :=
    norm_taoNormalizedPrimeCharacterSum_sub_primitiveCharacter_le_prime_mul
      (Z := Z) hp hq χ
  have hnorm : ‖taoNormalizedPrimeCharacterSum χ Z‖ ≤
      ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ +
        4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹ := by
    calc
      ‖taoNormalizedPrimeCharacterSum χ Z‖ =
          ‖(taoNormalizedPrimeCharacterSum χ Z -
            taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z) +
              taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ := by ring_nf
      _ ≤ ‖taoNormalizedPrimeCharacterSum χ Z -
            taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ +
          ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ := norm_add_le _ _
      _ ≤ ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ +
          4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹ := by linarith
  calc
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) ≤
        (‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ +
          4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 1000
    _ ≤ (2 : ℝ) ^ (1000 - 1) *
        (‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ) +
          (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by
      exact add_pow_le (norm_nonneg _)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg _))) 1000
    _ = (2 : ℝ) ^ 999 *
        (‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ) +
          (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by norm_num

/-- Full product-modulus ambient moment at one scale, with the explicit
change-level collision correction. -/
theorem sum_nonprincipalPrimeProduct_pow_thousand_le_withCollisions
    {p q Z : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsIn
        ((p * q).divisors.erase 1) Z) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) *
            (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by
  let δ : ℝ := (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)
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
        (((p * q : ℕ) : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) * δ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply add_le_add
      · exact taoPrimitiveCounterpartMomentSum_le_unexceptional_divisors
          (Nat.mul_pos hp.pos hq.pos) hZ hExceptional
      · apply mul_le_mul_of_nonneg_right _ (pow_nonneg
          (mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg _))) _)
        exact_mod_cast card_taoNonprincipalCharacters_le_totient
          (p * q) (Nat.mul_pos hp.pos hq.pos)
    _ = (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) *
            (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by rfl

/-- Coordinate-summed ambient product-modulus moment with no band-separation
hypothesis. -/
theorem sum_nonprincipalPrimeProduct_coordinateMoments_le_withCollisions
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((p * q).divisors.erase 1) P) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (P j : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters (p * q),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (2 : ℝ) ^ 999 *
            (((p * q : ℕ) : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)) +
              ((p * q).totient : ℝ) *
                (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                  (1000 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeProduct_pow_thousand_le_withCollisions
        hp hq (hP j)
      intro d hd hpBad
      apply hExceptional d hd
      rw [taoLargePrimeExceptionalConductorsFor, Finset.mem_biUnion]
      exact ⟨j, hj, hpBad⟩
    _ = (2 : ℝ) ^ 999 *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (((p * q : ℕ) : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)) +
            ((p * q).totient : ℝ) *
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                (1000 : ℕ)) := by
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (P j : ℝ) ^ (-(8 : ℝ)) +
          ((p * q).totient : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                (1000 : ℕ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Proposition 6.8's product-modulus deviation estimate with change-level
collisions fully accounted for and no band-separation hypothesis. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_unexceptional
    {p q a m' : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : Nat.Coprime a (p * q)) (hm : Nat.Coprime m' (p * q))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((p * q).divisors.erase 1) P) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        ((2 * ∑ j : Fin 1001,
            ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
          (2 : ℝ) ^ 999 *
            (((p * q : ℕ) : ℝ) *
                ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                  (P j : ℝ) ^ (-(8 : ℝ)) +
              ((p * q).totient : ℝ) *
                ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                  (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                    (1000 : ℕ))) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime_mul
    hp hq ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment :=
    sum_nonprincipalPrimeProduct_coordinateMoments_le_withCollisions
      hp hq P hP hExceptional
  gcongr

end

end Tao2026
