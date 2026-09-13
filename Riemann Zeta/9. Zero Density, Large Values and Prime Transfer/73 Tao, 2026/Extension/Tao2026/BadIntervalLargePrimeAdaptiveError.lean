import Tao2026.BadIntervalLargePrimeAdaptiveExceptional

/-!
# Adaptive character errors for the large-prime blocks

The adaptive exceptional families have the cardinalities required by Tao's
modulus-band partition.  This module supplies their finite consumer
interface: outside an adaptive family, every primitive nonprincipal
character lies below the adaptive threshold.  The resulting 1000th-moment
bound is then inserted into the one-prime residue-fiber estimate.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- The complete primitive-nonprincipal family has cardinality at most the
full character group, hence at most Euler's totient. -/
theorem card_taoPrimitiveNonprincipalCharacters_le_totient
    (q : ℕ) (hq : 0 < q) :
    (taoPrimitiveNonprincipalCharacters q).card ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (taoPrimitiveNonprincipalCharacters q).card ≤
        Fintype.card (DirichletCharacter ℂ q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card fun χ _hχ => Finset.mem_univ χ
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- If the adaptive exceptional fiber is empty, the complete primitive
nonprincipal 1000th moment is bounded by its totient-sized threshold mass. -/
theorem sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le_adaptive
    (q Z R : ℕ) (hq : 0 < q)
    (hEmpty : taoLargePrimeAdaptiveExceptionalCharacters q Z R = ∅) :
    (∑ χ ∈ taoPrimitiveNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (q.totient : ℝ) *
        taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) := by
  have hpoint : ∀ χ ∈ taoPrimitiveNonprincipalCharacters q,
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) ≤
        taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) := by
    intro χ hχ
    have hdata := mem_taoPrimitiveNonprincipalCharacters.mp hχ
    have hnorm : ‖taoNormalizedPrimeCharacterSum χ Z‖ <
        taoLargePrimeAdaptiveThreshold Z R := by
      by_contra hnot
      have hadaptive : taoLargePrimeAdaptiveThreshold Z R ≤
          ‖taoNormalizedPrimeCharacterSum χ Z‖ := le_of_not_gt hnot
      have hfixed : taoExceptionalPrimeCharacterThreshold Z ≤
          ‖taoNormalizedPrimeCharacterSum χ Z‖ :=
        (le_max_left _ _).trans hadaptive
      have hfixedMem : χ ∈ taoExceptionalPrimitiveCharacters q Z :=
        mem_taoExceptionalPrimitiveCharacters.mpr
          ⟨hdata.1, hdata.2, hfixed⟩
      have hadaptiveMem :
          χ ∈ taoLargePrimeAdaptiveExceptionalCharacters q Z R :=
        mem_taoLargePrimeAdaptiveExceptionalCharacters.mpr
          ⟨hfixedMem, hadaptive⟩
      rw [hEmpty] at hadaptiveMem
      simp at hadaptiveMem
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm.le 1000
  have hsum := Finset.sum_le_card_nsmul
    (taoPrimitiveNonprincipalCharacters q)
    (fun χ : DirichletCharacter ℂ q =>
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ))
    (taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ)) hpoint
  calc
    (∑ χ ∈ taoPrimitiveNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
        (taoPrimitiveNonprincipalCharacters q).card *
          taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) := by
      simpa only [nsmul_eq_mul] using hsum
    _ ≤ (q.totient : ℝ) *
        taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _
        (pow_nonneg (taoLargePrimeAdaptiveThreshold_nonneg Z R) _)
      exact_mod_cast card_taoPrimitiveNonprincipalCharacters_le_totient q hq

/-- A conductor outside the adaptive exceptional-conductor set has an empty
adaptive character fiber. -/
theorem taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
    {D : Finset ℕ} {q Z R : ℕ} (hqD : q ∈ D)
    (hqExceptional :
      q ∉ taoLargePrimeAdaptiveExceptionalConductorsIn D Z R) :
    taoLargePrimeAdaptiveExceptionalCharacters q Z R = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hNonempty
  apply hqExceptional
  simp [taoLargePrimeAdaptiveExceptionalConductorsIn, hqD, hNonempty]

/-- Prime-level adaptive 1000th-moment estimate outside the adaptive
exceptional-conductor set. -/
theorem sum_nonprincipalPrimeCharacter_pow_thousand_le_of_not_adaptiveExceptional
    {D : Finset ℕ} {p Z R : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (hpExceptional :
      p ∉ taoLargePrimeAdaptiveExceptionalConductorsIn D Z R) :
    (∑ χ ∈ taoNonprincipalCharacters p,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (p.totient : ℝ) *
        taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) := by
  rw [taoNonprincipalCharacters_eq_primitive_of_prime hp]
  exact sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le_adaptive
    p Z R hp.pos
      (taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
        hpD hpExceptional)

/-- The exact adaptive 1000th-moment mass over the 1000 ordinary tuple
coordinates. -/
def taoLargePrimeAdaptiveMomentSum
    (P : Fin 1001 → ℕ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
    taoLargePrimeAdaptiveThreshold (P j) R ^ (1000 : ℕ)

theorem taoLargePrimeAdaptiveMomentSum_nonneg
    (P : Fin 1001 → ℕ) (R : ℕ) :
    0 ≤ taoLargePrimeAdaptiveMomentSum P R := by
  unfold taoLargePrimeAdaptiveMomentSum
  positivity

/-- The modulus-band part of the adaptive threshold has exact 1000th power
`R⁻¹⁰`. -/
theorem taoLargePrimeAdaptiveBandThreshold_pow_thousand (R : ℕ) :
    ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (1000 : ℕ) =
      (R : ℝ) ^ (-(10 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg R)]
  congr 1
  norm_num

/-- The 1000th power of the maximum defining the adaptive threshold is
bounded by the sum of the fixed source tail and the new band-scale tail. -/
theorem taoLargePrimeAdaptiveThreshold_pow_thousand_le
    (Z R : ℕ) :
    taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) ≤
      (Z : ℝ) ^ (-(8 : ℝ)) + (R : ℝ) ^ (-(10 : ℝ)) := by
  have hmax :
      taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) ≤
        taoExceptionalPrimeCharacterThreshold Z ^ (1000 : ℕ) +
          ((R : ℝ) ^ (-(1 / 100 : ℝ))) ^ (1000 : ℕ) := by
    unfold taoLargePrimeAdaptiveThreshold
    by_cases h : taoExceptionalPrimeCharacterThreshold Z ≤
        (R : ℝ) ^ (-(1 / 100 : ℝ))
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left
        (pow_nonneg (taoExceptionalPrimeCharacterThreshold_nonneg Z) _)
    · rw [max_eq_left (le_of_not_ge h)]
      exact le_add_of_nonneg_right
        (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg R) _) _)
  calc
    taoLargePrimeAdaptiveThreshold Z R ^ (1000 : ℕ) ≤ _ := hmax
    _ = (Z : ℝ) ^ (-(8 : ℝ)) + (R : ℝ) ^ (-(10 : ℝ)) := by
      rw [taoExceptionalPrimeCharacterThreshold_pow_thousand,
        taoLargePrimeAdaptiveBandThreshold_pow_thousand]

/-- The full adaptive coordinate moment is the old eighth-power mass plus at
most 1000 copies of the new `R⁻¹⁰` tail. -/
theorem taoLargePrimeAdaptiveMomentSum_le
    (P : Fin 1001 → ℕ) (R : ℕ) :
    taoLargePrimeAdaptiveMomentSum P R ≤
      taoPrimeTupleEighthPowerSum P +
        1000 * (R : ℝ) ^ (-(10 : ℝ)) := by
  unfold taoLargePrimeAdaptiveMomentSum
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoLargePrimeAdaptiveThreshold (P j) R ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ((P j : ℝ) ^ (-(8 : ℝ)) +
            (R : ℝ) ^ (-(10 : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact taoLargePrimeAdaptiveThreshold_pow_thousand_le (P j) R
    _ = taoPrimeTupleEighthPowerSum P +
        1000 * (R : ℝ) ^ (-(10 : ℝ)) := by
      rw [Finset.sum_add_distrib]
      simp [taoPrimeTupleEighthPowerSum]

/-- Outside the coordinate-wise adaptive exceptional union, the complete
nonprincipal moment is bounded by the exact summed adaptive threshold mass. -/
theorem sum_nonprincipalPrimeCharacter_coordinateMoments_le_adaptive
    {D : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (P : Fin 1001 → ℕ) (R : ℕ)
    (hpExceptional :
      p ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    (∑ χ ∈ taoNonprincipalCharacters p,
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      (p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters p,
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (p.totient : ℝ) *
            taoLargePrimeAdaptiveThreshold (P j) R ^ (1000 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeCharacter_pow_thousand_le_of_not_adaptiveExceptional
        hp hpD
      intro hpBad
      apply hpExceptional
      rw [taoLargePrimeAdaptiveExceptionalConductorsFor, Finset.mem_biUnion]
      exact ⟨j, hj, hpBad⟩
    _ = (p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R := by
      rw [taoLargePrimeAdaptiveMomentSum, Finset.mul_sum]

/-- Complete explicit error accompanying the one-prime main term when the
adaptive exceptional family at modulus-band scale `R` is removed. -/
def taoLargePrimeAdaptiveImprovedError
    (P : Fin 1001 → ℕ) (p R : ℕ) : ℝ :=
  (p.totient : ℝ)⁻¹ *
    (taoPrimeTupleBandReciprocalSum P +
      (p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R)

theorem taoLargePrimeAdaptiveImprovedError_nonneg
    (P : Fin 1001 → ℕ) (p R : ℕ) :
    0 ≤ taoLargePrimeAdaptiveImprovedError P p R := by
  unfold taoLargePrimeAdaptiveImprovedError
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (add_nonneg (taoPrimeTupleBandReciprocalSum_nonneg P)
      (mul_nonneg (by positivity)
        (taoLargePrimeAdaptiveMomentSum_nonneg P R)))

/-- The adaptive one-prime error differs from the fixed-threshold error by
at most the explicit `1000 R⁻¹⁰` tail. -/
theorem taoLargePrimeAdaptiveImprovedError_le_fixed_add
    (P : Fin 1001 → ℕ) {p R : ℕ} (hp : Nat.Prime p) :
    taoLargePrimeAdaptiveImprovedError P p R ≤
      taoLargePrimeImprovedError P p +
        1000 * (R : ℝ) ^ (-(10 : ℝ)) := by
  have hphi : (0 : ℝ) < (p.totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hAdaptive :
      taoLargePrimeAdaptiveImprovedError P p R =
        (p.totient : ℝ)⁻¹ * taoPrimeTupleBandReciprocalSum P +
          taoLargePrimeAdaptiveMomentSum P R := by
    rw [taoLargePrimeAdaptiveImprovedError, mul_add]
    congr 1
    field_simp
  have hFixed :
      taoLargePrimeImprovedError P p =
        (p.totient : ℝ)⁻¹ * taoPrimeTupleBandReciprocalSum P +
          taoPrimeTupleEighthPowerSum P := by
    rw [taoLargePrimeImprovedError, mul_add]
    unfold taoPrimeTupleEighthPowerSum
    congr 1
    field_simp
  rw [hAdaptive, hFixed]
  simpa [add_assoc] using add_le_add
    (le_refl ((p.totient : ℝ)⁻¹ * taoPrimeTupleBandReciprocalSum P))
    (taoLargePrimeAdaptiveMomentSum_le P R)

/-- Adaptive form of Proposition 6.7's residue-fiber deviation estimate. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_adaptive
    {D : Finset ℕ} {p a m' R : ℕ} (hp : Nat.Prime p) (hpD : p ∈ D)
    (ha : Nat.Coprime a p) (hm : Nat.Coprime m' p)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional :
      p ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p]} : ℝ) : ℂ) -
        (1 / (p.totient : ℂ))‖ ≤
      ‖(1 / (p.totient : ℂ))‖ *
        (taoPrimeTupleBandReciprocalSum P +
          (p.totient : ℝ) * taoLargePrimeAdaptiveMomentSum P R) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime
    hp ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment := sum_nonprincipalPrimeCharacter_coordinateMoments_le_adaptive
    (D := D) hp hpD P R hpExceptional
  unfold taoPrimeTupleBandReciprocalSum
  exact add_le_add le_rfl hMoment

/-- Absolute-deviation form of the adaptive one-prime probability estimate. -/
theorem abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    {D : Finset ℕ} {m' R : ℕ} (a : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hpD : a.2 ∈ D)
    (hpl : ¬a.2 ∣ a.1) (hm : Nat.Coprime m' a.2)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional :
      a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    |taoLargePrimeProbability P hP m' a - 1 / (a.2.totient : ℝ)| ≤
      taoLargePrimeAdaptiveImprovedError P a.2 R := by
  rcases taoLargePrimeDivisibilityEvent_empty_or_primitiveResidueClass
    hp hpl with hempty | ⟨r, hr, hset⟩
  · obtain ⟨w, hw⟩ :=
      taoLargePrimeDivisibilityEvent_nonempty_of_coprime_remainder a hp hm
    have hwEmpty : w ∈ (∅ : Set TaoPrimeTuple) := by
      rw [← hempty]
      exact hw
    simp at hwEmpty
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_adaptive
        hp hpD hr hm P hP hpExceptional
    rw [taoLargePrimeProbability, hset]
    have heq :
        (((taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} : ℝ) : ℂ) -
            (1 / (a.2.totient : ℂ)) =
          (((taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2]} -
            1 / (a.2.totient : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real] at hnorm
    simpa [taoLargePrimeAdaptiveImprovedError, one_div] using hnorm

/-- Literal upper half of the adaptive Proposition 6.7 estimate. -/
theorem taoLargePrimeProbability_le_main_add_adaptiveError
    {D : Finset ℕ} {m' R : ℕ} (a : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hpD : a.2 ∈ D)
    (hpl : ¬a.2 ∣ a.1) (hm : Nat.Coprime m' a.2)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional :
      a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    taoLargePrimeProbability P hP m' a ≤
      1 / (a.2.totient : ℝ) +
        taoLargePrimeAdaptiveImprovedError P a.2 R := by
  have habs := abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    a hp hpD hpl hm P hP hpExceptional
  nlinarith [le_trans (le_abs_self
    (taoLargePrimeProbability P hP m' a -
      1 / (a.2.totient : ℝ))) habs]

/-- The adaptive literal error retains the required `O(R^-1.001)` power
uniformly on every source-scale selected modulus band. -/
theorem eventually_taoLargePrimeAdaptiveImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ p : ℕ,
      p ∈ taoDyadicPrimeBand (R x) →
      taoLargePrimeAdaptiveImprovedError (P x) p (R x) ≤
        1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
  filter_upwards [eventually_taoLargePrimeImprovedError_le_sourcePower hscale hR,
    hR.eventually_two_le] with x hFixed hRtwo
  intro p hp
  have hDecay : (R x : ℝ) ^ (-(10 : ℝ)) ≤
      (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ R x by omega))
      (by norm_num)
  calc
    taoLargePrimeAdaptiveImprovedError (P x) p (R x) ≤
        taoLargePrimeImprovedError (P x) p +
          1000 * (R x : ℝ) ^ (-(10 : ℝ)) :=
      taoLargePrimeAdaptiveImprovedError_le_fixed_add (P x)
        (mem_taoDyadicPrimeBand.mp hp).1
    _ ≤ 3 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) +
        1000 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by
      exact add_le_add (hFixed p hp)
        (mul_le_mul_of_nonneg_left hDecay (by norm_num))
    _ = 1003 * (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) := by ring

/-! ## Product-modulus adaptive moments -/

/-- A fixed ambient conductor fiber is bounded by the adaptive threshold
whenever that conductor has no adaptive exceptional primitive character. -/
theorem taoFixedConductorPrimitiveMomentSum_le_adaptive
    (q d Z S : ℕ) [NeZero q] (hdPos : 0 < d) (hdOne : d ≠ 1)
    (hEmpty : taoLargePrimeAdaptiveExceptionalCharacters d Z S = ∅) :
    taoFixedConductorPrimitiveMomentSum q d Z ≤
      (d.totient : ℝ) *
        taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
  rw [taoFixedConductorPrimitiveMomentSum_eq_image]
  exact (sum_fixedConductorPrimitiveCharacter_pow_thousand_le q d Z hdOne).trans
    (sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le_adaptive
      d Z S hdPos hEmpty)

/-- Coprimality-free primitive-counterpart moment bound when every
nontrivial divisor conductor is adaptively unexceptional. -/
theorem taoPrimitiveCounterpartMomentSum_le_adaptive_divisors
    {q Z S : ℕ} (hq : 0 < q)
    (hExceptional : ∀ d ∈ q.divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsIn
        (q.divisors.erase 1) Z S) :
    taoPrimitiveCounterpartMomentSum q Z ≤
      (q : ℝ) * taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [taoPrimitiveCounterpartMomentSum_eq_sum_fixedConductors q Z hq]
  calc
    (∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z) ≤
        ∑ d ∈ q.divisors.erase 1,
          (d.totient : ℝ) *
            taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdMem : d ∈ q.divisors := Finset.mem_of_mem_erase hd
      have hdDvd : d ∣ q := (Nat.mem_divisors.mp hdMem).1
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDvd hq
      exact taoFixedConductorPrimitiveMomentSum_le_adaptive
        q d Z S hdPos (Finset.ne_of_mem_erase hd)
          (taoLargePrimeAdaptiveExceptionalCharacters_eq_empty_of_not_mem
            hd (hExceptional d hd))
    _ = ((∑ d ∈ q.divisors.erase 1, d.totient : ℕ) : ℝ) *
        taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (q : ℝ) *
        taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _
        (pow_nonneg (taoLargePrimeAdaptiveThreshold_nonneg Z S) _)
      exact_mod_cast sum_totient_divisors_erase_one_le q

/-- Product-modulus ambient moment at one coordinate after removing the
adaptive exceptional divisor conductors. -/
theorem sum_nonprincipalPrimeProduct_pow_thousand_le_adaptive_withCollisions
    {p q Z S : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsIn
        ((p * q).divisors.erase 1) Z S) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) *
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
        (((p * q : ℕ) : ℝ) *
            taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) +
          ((p * q).totient : ℝ) * δ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply add_le_add
      · exact taoPrimitiveCounterpartMomentSum_le_adaptive_divisors
          (Nat.mul_pos hp.pos hq.pos) hExceptional
      · apply mul_le_mul_of_nonneg_right _ (pow_nonneg
          (mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg _))) _)
        exact_mod_cast card_taoNonprincipalCharacters_le_totient
          (p * q) (Nat.mul_pos hp.pos hq.pos)
    _ = (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) *
            taoLargePrimeAdaptiveThreshold Z S ^ (1000 : ℕ) +
          ((p * q).totient : ℝ) *
            (4 * ((taoDyadicPrimeBand Z).card : ℝ)⁻¹) ^ (1000 : ℕ)) := by rfl

/-- Coordinate-summed adaptive product-modulus moment, retaining the exact
change-level collision correction. -/
theorem sum_nonprincipalPrimeProduct_coordinateMoments_le_adaptive_withCollisions
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (P : Fin 1001 → ℕ) (S : ℕ)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
        ((p * q).divisors.erase 1) P S) :
    (∑ χ ∈ taoNonprincipalCharacters (p * q),
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) * taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P) := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        ∑ χ ∈ taoNonprincipalCharacters (p * q),
          ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ)) ≤
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (2 : ℝ) ^ 999 *
            (((p * q : ℕ) : ℝ) *
                taoLargePrimeAdaptiveThreshold (P j) S ^ (1000 : ℕ) +
              ((p * q).totient : ℝ) *
                (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                  (1000 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sum_nonprincipalPrimeProduct_pow_thousand_le_adaptive_withCollisions
        hp hq
      intro d hd hdBad
      apply hExceptional d hd
      rw [taoLargePrimeAdaptiveExceptionalConductorsFor, Finset.mem_biUnion]
      exact ⟨j, hj, hdBad⟩
    _ = (2 : ℝ) ^ 999 *
        ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
          (((p * q : ℕ) : ℝ) *
              taoLargePrimeAdaptiveThreshold (P j) S ^ (1000 : ℕ) +
            ((p * q).totient : ℝ) *
              (4 * ((taoDyadicPrimeBand (P j)).card : ℝ)⁻¹) ^
                (1000 : ℕ)) := by
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) * taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P) := by
      unfold taoLargePrimeAdaptiveMomentSum
      unfold taoPrimeTupleChangeLevelCollisionSum
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Complete product-modulus error after removing adaptive exceptional
divisor conductors at partner-band scale `S`. -/
def taoLargePrimeAdaptiveJointImprovedError
    (P : Fin 1001 → ℕ) (p q S : ℕ) : ℝ :=
  ((p * q).totient : ℝ)⁻¹ *
    (2 * taoPrimeTupleBandReciprocalSum P +
      (2 : ℝ) ^ 999 *
        (((p * q : ℕ) : ℝ) * taoLargePrimeAdaptiveMomentSum P S +
          ((p * q).totient : ℝ) *
            taoPrimeTupleChangeLevelCollisionSum P))

theorem taoLargePrimeAdaptiveJointImprovedError_nonneg
    (P : Fin 1001 → ℕ) (p q S : ℕ) :
    0 ≤ taoLargePrimeAdaptiveJointImprovedError P p q S := by
  unfold taoLargePrimeAdaptiveJointImprovedError
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply add_nonneg
  · exact mul_nonneg (by norm_num)
      (taoPrimeTupleBandReciprocalSum_nonneg P)
  · apply mul_nonneg (pow_nonneg (by norm_num) _)
    exact add_nonneg
      (mul_nonneg (by positivity)
        (taoLargePrimeAdaptiveMomentSum_nonneg P S))
      (mul_nonneg (by positivity)
        (taoPrimeTupleChangeLevelCollisionSum_nonneg P))

/-- Adaptive product-modulus residue-fiber deviation estimate. -/
theorem primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_adaptive
    {p q a m' S : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : Nat.Coprime a (p * q)) (hm : Nat.Coprime m' (p * q))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (p * q).divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
        ((p * q).divisors.erase 1) P S) :
    ‖(((taoPrimeTupleMeasure P hP).real
        {ω | taoPrimeTupleStart m' ω ≡ a [MOD p * q]} : ℝ) : ℂ) -
        (1 / ((p * q).totient : ℂ))‖ ≤
      ‖(1 / ((p * q).totient : ℂ))‖ *
        (2 * taoPrimeTupleBandReciprocalSum P +
          (2 : ℝ) ^ 999 *
            (((p * q : ℕ) : ℝ) * taoLargePrimeAdaptiveMomentSum P S +
              ((p * q).totient : ℝ) *
                taoPrimeTupleChangeLevelCollisionSum P)) := by
  refine (primitiveResidueFiber_probability_sub_main_norm_le_prime_mul
    hp hq ha hm P hP).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hMoment :=
    sum_nonprincipalPrimeProduct_coordinateMoments_le_adaptive_withCollisions
      hp hq P S hExceptional
  unfold taoPrimeTupleBandReciprocalSum taoPrimeTupleChangeLevelCollisionSum
  exact add_le_add le_rfl hMoment

/-- Literal joint probability upper bound outside the adaptive divisor
conductors. -/
theorem taoLargePrimeJointProbability_le_main_add_adaptiveError
    {m' S : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hExceptional : ∀ d ∈ (a.2 * b.2).divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
        ((a.2 * b.2).divisors.erase 1) P S) :
    taoLargePrimeJointProbability P hP m' a b ≤
      1 / ((a.2 * b.2).totient : ℝ) +
        taoLargePrimeAdaptiveJointImprovedError P a.2 b.2 S := by
  rcases taoLargePrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    hp hq hpq hpa hqb with hempty | ⟨r, hr, hset⟩
  · rw [taoLargePrimeJointProbability, hempty, MeasureTheory.measureReal_empty]
    exact add_nonneg (by positivity)
      (taoLargePrimeAdaptiveJointImprovedError_nonneg P a.2 b.2 S)
  · have hnorm :=
      primitiveResidueFiber_probability_sub_main_norm_le_prime_mul_adaptive
        hp hq hr hm P hP hExceptional
    rw [taoLargePrimeJointProbability, hset]
    have hreal :
        |(taoPrimeTupleMeasure P hP).real
              {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
            1 / ((a.2 * b.2).totient : ℝ)| ≤
          taoLargePrimeAdaptiveJointImprovedError P a.2 b.2 S := by
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
      simpa [taoLargePrimeAdaptiveJointImprovedError, one_div] using hnorm
    nlinarith [le_trans (le_abs_self
      ((taoPrimeTupleMeasure P hP).real
          {w | taoPrimeTupleStart m' w ≡ r [MOD a.2 * b.2]} -
        1 / ((a.2 * b.2).totient : ℝ))) hreal]

/-- The adaptive joint error differs from the fixed-threshold joint error by
at most `2^999 · 4000 · S⁻¹⁰`. -/
theorem taoLargePrimeAdaptiveJointImprovedError_le_fixed_add
    (P : Fin 1001 → ℕ) {p q S : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    taoLargePrimeAdaptiveJointImprovedError P p q S ≤
      taoLargePrimeJointImprovedError P p q +
        (2 : ℝ) ^ 999 * 4000 * (S : ℝ) ^ (-(10 : ℝ)) := by
  have hpqPos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hphi : (0 : ℝ) < ((p * q).totient : ℕ) := by
    exact_mod_cast Nat.totient_pos.mpr hpqPos
  let A : ℝ := ((p * q).totient : ℝ)⁻¹ *
    (2 * taoPrimeTupleBandReciprocalSum P)
  let c : ℝ := (2 : ℝ) ^ 999
  let ρ : ℝ := ((p * q : ℕ) : ℝ) / ((p * q).totient : ℝ)
  let V : ℝ := taoPrimeTupleEighthPowerSum P
  let M : ℝ := taoLargePrimeAdaptiveMomentSum P S
  let W : ℝ := taoPrimeTupleChangeLevelCollisionSum P
  let T : ℝ := (S : ℝ) ^ (-(10 : ℝ))
  have hAdaptive :
      taoLargePrimeAdaptiveJointImprovedError P p q S =
        A + c * (ρ * M + W) := by
    dsimp [A, c, ρ, M, W]
    rw [taoLargePrimeAdaptiveJointImprovedError]
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
  have hρ : ρ ≤ 4 := by
    exact natCast_mul_div_totient_mul_le_four hp hq hpq
  have hρnonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hM : M ≤ V + 1000 * T := by
    exact taoLargePrimeAdaptiveMomentSum_le P S
  have hcNonneg : 0 ≤ c := pow_nonneg (by norm_num) 999
  have hcore : ρ * M ≤ ρ * V + 4000 * T := by
    calc
      ρ * M ≤ ρ * (V + 1000 * T) :=
        mul_le_mul_of_nonneg_left hM hρnonneg
      _ = ρ * V + ρ * (1000 * T) := by ring
      _ ≤ ρ * V + 4 * (1000 * T) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hρ (mul_nonneg (by norm_num) hTnonneg))
      _ = ρ * V + 4000 * T := by ring
  rw [hAdaptive, hFixed]
  calc
    A + c * (ρ * M + W) ≤
        A + c * ((ρ * V + 4000 * T) + W) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add hcore le_rfl) hcNonneg)
    _ = A + c * (ρ * V + W) + c * 4000 * T := by
      rw [show (ρ * V + 4000 * T) + W =
        (ρ * V + W) + 4000 * T by ac_rfl]
      rw [mul_add, ← add_assoc, mul_assoc]
    _ = A + c * (ρ * V + W) +
        (2 : ℝ) ^ 999 * 4000 * (S : ℝ) ^ (-(10 : ℝ)) := by rfl

/-- Explicit constant for the adaptive joint source-power error. -/
def taoLargePrimeAdaptiveSourceJointPowerConstant : ℝ :=
  taoLargePrimeSourceJointPowerConstant + (2 : ℝ) ^ 999 * 4000

private theorem adaptive_joint_tail_le_ordered_power
    {R S : ℕ} (hR : 0 < R) (hS : 1 ≤ S) (hRS : R ≤ S) :
    (S : ℝ) ^ (-(10 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S : ℝ) ^ (-(1 : ℝ)) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hSreal : (0 : ℝ) < S := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hS)
  have hRSreal : (R : ℝ) ≤ S := by exact_mod_cast hRS
  have hNine : (S : ℝ) ^ (-(9 : ℝ)) ≤
      (S : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hS) (by norm_num)
  have hCross : (S : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤
      (R : ℝ) ^ (-(1001 / 1000 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hRreal hRSreal (by norm_num)
  rw [show (-(10 : ℝ)) = -(9 : ℝ) + -(1 : ℝ) by ring,
    Real.rpow_add hSreal]
  exact mul_le_mul_of_nonneg_right (hNine.trans hCross) (by positivity)

/-- On ordered source bands, the adaptive literal joint error retains the
required `O(R^-1.001 S^-1)` power. -/
theorem eventually_taoLargePrimeAdaptiveJointImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in Filter.atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeAdaptiveJointImprovedError (P x) p q (S x) ≤
        taoLargePrimeAdaptiveSourceJointPowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [eventually_taoLargePrimeJointImprovedError_le_sourcePower
      hscale hR hS, hR.eventually_two_le, hS.eventually_two_le, hRS] with
      x hFixed hRtwo hStwo hRSx
  intro p q hp hq hpq
  let T : ℝ := (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
    (S x : ℝ) ^ (-(1 : ℝ))
  have hTail : (S x : ℝ) ^ (-(10 : ℝ)) ≤ T :=
    adaptive_joint_tail_le_ordered_power (by omega) (by omega) hRSx
  have hFixedT : taoLargePrimeJointImprovedError (P x) p q ≤
      taoLargePrimeSourceJointPowerConstant * T := by
    dsimp only [T]
    rw [← mul_assoc]
    exact hFixed p q hp hq hpq
  calc
    taoLargePrimeAdaptiveJointImprovedError (P x) p q (S x) ≤
        taoLargePrimeJointImprovedError (P x) p q +
          (2 : ℝ) ^ 999 * 4000 * (S x : ℝ) ^ (-(10 : ℝ)) :=
      taoLargePrimeAdaptiveJointImprovedError_le_fixed_add
        (P x) (mem_taoDyadicPrimeBand.mp hp).1
          (mem_taoDyadicPrimeBand.mp hq).1 hpq
    _ ≤ taoLargePrimeSourceJointPowerConstant * T +
        (2 : ℝ) ^ 999 * 4000 * T := by
      exact add_le_add hFixedT
        (mul_le_mul_of_nonneg_left hTail (by positivity))
    _ = taoLargePrimeAdaptiveSourceJointPowerConstant *
        (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S x : ℝ) ^ (-(1 : ℝ)) := by
      rw [taoLargePrimeAdaptiveSourceJointPowerConstant]
      rw [mul_assoc
        (taoLargePrimeSourceJointPowerConstant + (2 : ℝ) ^ 999 * 4000)
        ((R x : ℝ) ^ (-(1001 / 1000 : ℝ)))
        ((S x : ℝ) ^ (-(1 : ℝ))), add_mul]

/-! ## Adaptive covariance errors -/

/-- Complete covariance error using adaptive marginal scales `R,S` and the
adaptive product-conductor scale `S`. -/
def taoLargePrimeAdaptiveCovarianceImprovedError
    (P : Fin 1001 → ℕ) (p q R S : ℕ) : ℝ :=
  taoLargePrimeAdaptiveJointImprovedError P p q S +
    (1 / (p.totient : ℝ)) * taoLargePrimeAdaptiveImprovedError P q S +
    (1 / (q.totient : ℝ)) * taoLargePrimeAdaptiveImprovedError P p R +
    taoLargePrimeAdaptiveImprovedError P p R *
      taoLargePrimeAdaptiveImprovedError P q S

/-- Adaptive covariance estimate with separate marginal exceptional sets
and the adaptive product-divisor exceptional set. -/
theorem taoLargePrimeCovariance_le_adaptiveErrors
    {m' R S : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hpa : ¬a.2 ∣ a.1) (hqb : ¬b.2 ∣ b.1)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {Dp Dq : Finset ℕ} (hpD : a.2 ∈ Dp) (hqD : b.2 ∈ Dq)
    (hpExceptional :
      a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor Dp P R)
    (hqExceptional :
      b.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor Dq P S)
    (hpqExceptional : ∀ d ∈ (a.2 * b.2).divisors.erase 1,
      d ∉ taoLargePrimeAdaptiveExceptionalConductorsFor
        ((a.2 * b.2).divisors.erase 1) P S) :
    taoLargePrimeCovariance P hP m' a b ≤
      taoLargePrimeAdaptiveCovarianceImprovedError P a.2 b.2 R S := by
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
  have hJ := taoLargePrimeJointProbability_le_main_add_adaptiveError
    a b hp hq hpq hpa hqb hm P hP hpqExceptional
  rw [hmain] at hJ
  have ha := abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    a hp hpD hpa hmParts.1 P hP hpExceptional
  have hb := abs_taoLargePrimeProbability_sub_main_le_adaptiveError
    b hq hqD hqb hmParts.2 P hP hqExceptional
  rw [taoLargePrimeCovariance]
  unfold taoLargePrimeAdaptiveCovarianceImprovedError
  exact sub_mul_le_of_abs_sub_le hJ ha hb
    (by positivity) (by positivity)
      (taoLargePrimeAdaptiveImprovedError_nonneg P a.2 R)

/-- Explicit constant for the ordered adaptive covariance source-power
error. -/
def taoLargePrimeAdaptiveSourceCovariancePowerConstant : ℝ :=
  taoLargePrimeAdaptiveSourceJointPowerConstant + 1010021

private theorem adaptive_selector_cross_power_le
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

/-- The adaptive covariance error retains the ordered-band
`O(R^-1.001 S^-1)` power. -/
theorem eventually_taoLargePrimeAdaptiveCovarianceImprovedError_le_sourcePower
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeSourceBandSelector R)
    (hS : TaoLargePrimeSourceBandSelector S)
    (hRS : ∀ᶠ x : ℕ in Filter.atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ p q : ℕ,
      p ∈ taoDyadicPrimeBand (R x) → q ∈ taoDyadicPrimeBand (S x) →
      p ≠ q →
      taoLargePrimeAdaptiveCovarianceImprovedError
          (P x) p q (R x) (S x) ≤
        taoLargePrimeAdaptiveSourceCovariancePowerConstant *
          (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
          (S x : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [
    eventually_taoLargePrimeAdaptiveJointImprovedError_le_sourcePower
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
      taoLargePrimeAdaptiveJointImprovedError (P x) p q (S x) ≤
        taoLargePrimeAdaptiveSourceJointPowerConstant * T := by
    dsimp only [T, A, B]
    rw [← mul_assoc]
    exact hJoint p q hp hq hpq
  have hERnonneg : 0 ≤ ER :=
    taoLargePrimeAdaptiveImprovedError_nonneg (P x) p (R x)
  have hESnonneg : 0 ≤ ES :=
    taoLargePrimeAdaptiveImprovedError_nonneg (P x) q (S x)
  have hCross : (R x : ℝ) ^ (-(1 : ℝ)) *
      (S x : ℝ) ^ (-(1001 / 1000 : ℝ)) ≤ T := by
    exact adaptive_selector_cross_power_le (by omega) (by omega) hRSx
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
  unfold taoLargePrimeAdaptiveCovarianceImprovedError
  calc
    taoLargePrimeAdaptiveJointImprovedError (P x) p q (S x) +
          (1 / (p.totient : ℝ)) * ES +
          (1 / (q.totient : ℝ)) * ER + ER * ES ≤
        taoLargePrimeAdaptiveSourceJointPowerConstant * T +
          2006 * T + 2006 * T + 1006009 * T := by
      exact add_le_add (add_le_add (add_le_add
        hJointT hMarginalS) hMarginalR) hProduct
    _ = taoLargePrimeAdaptiveSourceCovariancePowerConstant *
        (R x : ℝ) ^ (-(1001 / 1000 : ℝ)) *
        (S x : ℝ) ^ (-(1 : ℝ)) := by
      rw [hcombine]
      rw [taoLargePrimeAdaptiveSourceCovariancePowerConstant]
      dsimp only [T, A, B]
      rw [← mul_assoc]

end

end Tao2026
