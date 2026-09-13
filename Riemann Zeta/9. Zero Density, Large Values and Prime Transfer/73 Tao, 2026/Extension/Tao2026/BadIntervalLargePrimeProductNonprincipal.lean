import Tao2026.BadIntervalLargePrimeNonprincipal
import Tao2026.SmallPrimeMertens

/-!
# Nonprincipal moments for a product modulus

This module proves the exact conductor-reduced unexceptional estimate needed
for the two-prime branch of Proposition 6.8 when the sampled dyadic bands are
coprime to the ambient modulus.  Every nonprincipal ambient character is
regrouped by its primitive conductor.  If every nontrivial divisor conductor
is unexceptional, the totient divisor identity bounds the complete moment by
`q Z⁻⁸`; summing over the ordinary tuple coordinates gives the desired
product-modulus error.  The companion product-collision module removes this
separation condition by quantifying the possible ambient-prime sample points.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- If all nontrivial conductor divisors are unexceptional and the prime band
is coprime to the ambient modulus, the complete nonprincipal ambient moment is
at most `q Z⁻⁸`. -/
theorem sum_nonprincipalPrimeCharacter_pow_thousand_le_unexceptional_divisors
    {q Z : ℕ} (hq : 0 < q) (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hcoprime : ∀ r ∈ taoDyadicPrimeBand Z, Nat.Coprime r q)
    (hExceptional : ∀ d ∈ q.divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsIn (q.divisors.erase 1) Z) :
    (∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (q : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [sum_nonprincipalPrimeCharacter_pow_thousand_eq_sum_fixedConductors
    q Z hq hcoprime]
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

/-- Coordinate-summed form for a product of two prime moduli.  The explicit
coprime-band assumption is the exact boundary of the current change-level
argument. -/
theorem sum_nonprincipalPrimeProduct_coordinateMoments_le
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hcoprime : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      ∀ r ∈ taoDyadicPrimeBand (P j), Nat.Coprime r (p * q))
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((p * q).divisors.erase 1) P) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      ((p * q : ℕ) : ℝ) *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (P j : ℝ) ^ (-(8 : ℝ)) := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters (p * q),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((p * q : ℕ) : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeCharacter_pow_thousand_le_unexceptional_divisors
        (Nat.mul_pos hp.pos hq.pos) (hP j) (hcoprime j hj)
      intro d hd hpBad
      apply hExceptional d hd
      rw [taoLargePrimeExceptionalConductorsFor, Finset.mem_biUnion]
      exact ⟨j, hj, hpBad⟩
    _ = ((p * q : ℕ) : ℝ) *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (P j : ℝ) ^ (-(8 : ℝ)) := by
      rw [Finset.mul_sum]

/-- Product-modulus deviation estimate after the conductor split, under exact
band separation from both modulus primes. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_unexceptional_of_coprimeBands
    {p q a m' : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : Nat.Coprime a (p * q)) (hm : Nat.Coprime m' (p * q))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hcoprime : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      ∀ r ∈ taoDyadicPrimeBand (P j), Nat.Coprime r (p * q))
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeExceptionalConductorsFor
        ((p * q).divisors.erase 1) P) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        ((2 * ∑ j : Fin 1001,
            ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) +
          ((p * q : ℕ) : ℝ) *
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              (P j : ℝ) ^ (-(8 : ℝ))) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime_mul
    hp hq ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment := sum_nonprincipalPrimeProduct_coordinateMoments_le
    hp hq P hP hcoprime hExceptional
  gcongr

end

end Tao2026
