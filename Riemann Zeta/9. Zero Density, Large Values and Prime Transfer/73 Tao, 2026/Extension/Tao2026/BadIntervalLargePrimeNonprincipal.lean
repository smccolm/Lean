import Tao2026.BadIntervalLargePrimeExceptional
import Tao2026.BadIntervalPrincipalCharacter

/-!
# Nonprincipal moments for a large prime modulus

This module completes the elementary character-moment half of Tao's
Proposition 6.7.  Every nonprincipal character modulo a prime is primitive.
Consequently, after removing the conductors that are exceptional at one of
the 1000 ordinary tuple-coordinate scales, the full nonprincipal 1000th
moment is bounded by the explicit unexceptional error `φ(p) P_j⁻⁸` at each
coordinate.  The final theorem substitutes that estimate directly into the
principal-character collision bound.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- A nonprincipal character of prime level has full conductor. -/
theorem isPrimitive_of_prime_of_ne_one
    {p : ℕ} (hp : Nat.Prime p) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    DirichletCharacter.IsPrimitive χ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with hc | hc
  · exfalso
    apply hχ
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
    exact hc
  · exact hc

/-- At prime level the nonprincipal and primitive-nonprincipal character
finsets coincide exactly. -/
theorem taoNonprincipalCharacters_eq_primitive_of_prime
    {p : ℕ} (hp : Nat.Prime p) :
    taoNonprincipalCharacters p = taoPrimitiveNonprincipalCharacters p := by
  ext χ
  rw [mem_taoNonprincipalCharacters, mem_taoPrimitiveNonprincipalCharacters]
  exact ⟨fun hχ => ⟨isPrimitive_of_prime_of_ne_one hp hχ, hχ⟩,
    fun hχ => hχ.2⟩

/-- A prime conductor outside the exceptional set has only the explicit
unexceptional `φ(p) Z⁻⁸` 1000th-moment contribution. -/
theorem sum_nonprincipalPrimeCharacter_pow_thousand_le_of_not_exceptional
    {D : Finset ℕ} {p Z : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (hpExceptional : p ∉ taoLargePrimeExceptionalConductorsIn D Z)
    (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    (∑ χ ∈ taoNonprincipalCharacters p,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (p.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  have hEmpty : taoExceptionalPrimitiveCharacters p Z = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hNonempty
    apply hpExceptional
    simp [taoLargePrimeExceptionalConductorsIn, hpD, hNonempty]
  rw [taoNonprincipalCharacters_eq_primitive_of_prime hp]
  simpa [hEmpty] using
    (sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le
      p Z hp.pos hZ)

/-- Conductors exceptional at at least one of the 1000 ordinary tuple
coordinate scales. -/
def taoLargePrimeExceptionalConductorsFor
    (D : Finset ℕ) (P : Fin 1001 → ℕ) : Finset ℕ :=
  (Finset.univ.erase (0 : Fin 1001)).biUnion fun j =>
    taoLargePrimeExceptionalConductorsIn D (P j)

/-- The union over coordinate scales costs at most the sum of the individual
exceptional-conductor counts. -/
theorem card_taoLargePrimeExceptionalConductorsFor_le
    (D : Finset ℕ) (P : Fin 1001 → ℕ) :
    (taoLargePrimeExceptionalConductorsFor D P).card ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        (taoLargePrimeExceptionalConductorsIn D (P j)).card := by
  exact Finset.card_biUnion_le

/-- A uniform bound at every ordinary coordinate scale loses only the fixed
factor 1000 when the exceptional conductors are united. -/
theorem card_taoLargePrimeExceptionalConductorsFor_le_thousand_mul
    (D : Finset ℕ) (P : Fin 1001 → ℕ) (B : ℕ)
    (hB : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      (taoLargePrimeExceptionalConductorsIn D (P j)).card ≤ B) :
    (taoLargePrimeExceptionalConductorsFor D P).card ≤ 1000 * B := by
  calc
    (taoLargePrimeExceptionalConductorsFor D P).card ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (taoLargePrimeExceptionalConductorsIn D (P j)).card :=
      card_taoLargePrimeExceptionalConductorsFor_le D P
    _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin 1001), B := by
      exact Finset.sum_le_sum fun j hj => hB j hj
    _ = 1000 * B := by simp

/-- Outside the coordinate-wise exceptional-conductor union, the whole
nonprincipal contribution in the AM--GM character expansion has the source's
explicit `Z⁻⁸` saving at every ordinary coordinate. -/
theorem sum_nonprincipalPrimeCharacter_coordinateMoments_le
    {D : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional : p ∉ taoLargePrimeExceptionalConductorsFor D P) :
    (∑ χ ∈ taoNonprincipalCharacters p,
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      (p.totient : ℝ) *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (P j : ℝ) ^ (-(8 : ℝ)) := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters p,
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (p.totient : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeCharacter_pow_thousand_le_of_not_exceptional
        hp hpD
      · intro hpBad
        apply hpExceptional
        rw [taoLargePrimeExceptionalConductorsFor, Finset.mem_biUnion]
        exact ⟨j, hj, hpBad⟩
      · exact hP j
    _ = (p.totient : ℝ) *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (P j : ℝ) ^ (-(8 : ℝ)) := by
      rw [Finset.mul_sum]

/-- Proposition 6.7's source-shaped unexceptional deviation estimate.  Its
two visible errors are precisely the coordinate-collision probability and
the accumulated unexceptional character moment. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_unexceptional
    {D : Finset ℕ} {p a m' : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (ha : Nat.Coprime a p) (hm : Nat.Coprime m' p)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional : p ∉ taoLargePrimeExceptionalConductorsFor D P) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p]} : ℝ) : ℂ) -
        (1 / (p.totient : ℂ))‖ ≤
      ‖(1 / (p.totient : ℂ))‖ *
        ((∑ j : Fin 1001,
            ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
          (p.totient : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (P j : ℝ) ^ (-(8 : ℝ))) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime
    hp ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment := sum_nonprincipalPrimeCharacter_coordinateMoments_le
    (D := D) hp hpD P hP hpExceptional
  gcongr

end

end Tao2026
