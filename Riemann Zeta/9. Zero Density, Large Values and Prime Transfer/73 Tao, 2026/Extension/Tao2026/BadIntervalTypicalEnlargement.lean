import Tao2026.BadIntervalTypicalScales

/-!
# Enlarged prime-band representations for the typical count

After Proposition 6.6, Tao bounds the prime counts from the original bands
using separate enlarged bands: `[4P₀,8P₀)` for the distinguished squared
prime and `[2Pⱼ,4Pⱼ)` for the other coordinates.  The smooth remainder is
left unchanged.  This module formalizes that counting family and its map into
the literal one-term bad set.  The final bounded-multiplicity theorem across
all ordered scales is kept as a separate subsequent step.
-/

namespace Tao2026

open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 8000

/-- Lower endpoint of the enlarged coordinate band used in the source count. -/
def taoPrimeTupleEnlargedScale
    (P : Fin 1001 → ℕ) (j : Fin 1001) : ℕ :=
  if j = 0 then 4 * P j else 2 * P j

@[simp] theorem taoPrimeTupleEnlargedScale_zero
    (P : Fin 1001 → ℕ) :
    taoPrimeTupleEnlargedScale P 0 = 4 * P 0 := by
  simp [taoPrimeTupleEnlargedScale]

theorem taoPrimeTupleEnlargedScale_of_ne_zero
    (P : Fin 1001 → ℕ) {j : Fin 1001} (hj : j ≠ 0) :
    taoPrimeTupleEnlargedScale P j = 2 * P j := by
  simp [taoPrimeTupleEnlargedScale, hj]

/-- Cartesian support of the enlarged prime tuple. -/
def taoPrimeTupleEnlargedSupport (P : Fin 1001 → ℕ) :
    Finset TaoPrimeTuple :=
  Fintype.piFinset fun j =>
    taoDyadicPrimeBand (taoPrimeTupleEnlargedScale P j)

theorem mem_taoPrimeTupleEnlargedSupport
    {P : Fin 1001 → ℕ} {ω : TaoPrimeTuple} :
    ω ∈ taoPrimeTupleEnlargedSupport P ↔
      ∀ j, ω j ∈ taoDyadicPrimeBand (taoPrimeTupleEnlargedScale P j) := by
  simp [taoPrimeTupleEnlargedSupport]

theorem card_taoPrimeTupleEnlargedSupport (P : Fin 1001 → ℕ) :
    (taoPrimeTupleEnlargedSupport P).card =
      ∏ j, (taoDyadicPrimeBand (taoPrimeTupleEnlargedScale P j)).card := by
  exact Fintype.card_piFinset _

/-- The enlarged prime tuple paired with the same smooth-remainder family as
the Proposition 6.6 summation. -/
def taoPrimeTupleEnlargedRemainderPairs
    (P : Fin 1001 → ℕ) (x : ℕ) :
    Finset (Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSmoothRemainders x P).sigma fun _ =>
    taoPrimeTupleEnlargedSupport P

theorem mem_taoPrimeTupleEnlargedRemainderPairs
    {P : Fin 1001 → ℕ} {x : ℕ}
    {a : Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleEnlargedRemainderPairs P x ↔
      a.1 ∈ taoPrimeTupleSmoothRemainders x P ∧
        a.2 ∈ taoPrimeTupleEnlargedSupport P := by
  simp [taoPrimeTupleEnlargedRemainderPairs]

/-- Exact cardinality of the source's enlarged counting family. -/
theorem card_taoPrimeTupleEnlargedRemainderPairs
    (P : Fin 1001 → ℕ) (x : ℕ) :
    (taoPrimeTupleEnlargedRemainderPairs P x).card =
      psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) *
        ∏ j, (taoDyadicPrimeBand
          (taoPrimeTupleEnlargedScale P j)).card := by
  rw [taoPrimeTupleEnlargedRemainderPairs, Finset.card_sigma]
  calc
    ∑ _m' ∈ taoPrimeTupleSmoothRemainders x P,
        (taoPrimeTupleEnlargedSupport P).card =
        (taoPrimeTupleSmoothRemainders x P).card *
          (taoPrimeTupleEnlargedSupport P).card := by simp
    _ = psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) *
        ∏ j, (taoDyadicPrimeBand
          (taoPrimeTupleEnlargedScale P j)).card := by
      rw [card_taoPrimeTupleSmoothRemainders,
        card_taoPrimeTupleEnlargedSupport]

/-- Integer represented by one enlarged remainder/prime-tuple pair. -/
def taoPrimeTupleEnlargedRemainderValue
    (a : Σ _m' : ℕ, TaoPrimeTuple) : ℕ :=
  taoPrimeTupleStart a.1 a.2

/-- Fixed dilation incurred by the enlarged bands: two occurrences of the
distinguished coordinate cost `8²`, and the 1000 tail coordinates cost one
factor `4` each. -/
def taoPrimeTupleEnlargementFactor : ℕ :=
  8 ^ 2 * ∏ _j ∈ (Finset.univ.erase (0 : Fin 1001)), 4

/-- A convenient exact finite endpoint before the fixed dilation is
simplified. -/
def taoPrimeTupleEnlargedAmbientBound
    (x : ℕ) (P : Fin 1001 → ℕ) : ℕ :=
  ((8 * P 0) ^ 2 *
      ∏ j ∈ (Finset.univ.erase (0 : Fin 1001)), 4 * P j) *
    taoPrimeTupleRemainderBudget x P

theorem taoPrimeTupleEnlargedScaleProduct_eq_factor_mul_denominator
    (P : Fin 1001 → ℕ) :
    (8 * P 0) ^ 2 *
        ∏ j ∈ (Finset.univ.erase (0 : Fin 1001)), 4 * P j =
      taoPrimeTupleEnlargementFactor * taoPrimeTupleScaleDenominator P := by
  rw [Finset.prod_mul_distrib]
  unfold taoPrimeTupleEnlargementFactor taoPrimeTupleScaleDenominator
  ring

theorem taoPrimeTupleEnlargedAmbientBound_le_fixed_mul
    (x : ℕ) (P : Fin 1001 → ℕ) :
    taoPrimeTupleEnlargedAmbientBound x P ≤
      2 * taoPrimeTupleEnlargementFactor * x := by
  rw [taoPrimeTupleEnlargedAmbientBound,
    taoPrimeTupleEnlargedScaleProduct_eq_factor_mul_denominator]
  unfold taoPrimeTupleRemainderBudget
  rw [Nat.mul_assoc]
  refine (Nat.mul_le_mul_left taoPrimeTupleEnlargementFactor
    (Nat.mul_div_le (2 * x) (taoPrimeTupleScaleDenominator P))).trans_eq ?_
  ac_rfl

/-- Every enlarged representation stays inside the explicit fixed dilation
of `[1,x]`. -/
theorem taoPrimeTupleEnlargedRemainderValue_le_ambientBound
    {P : Fin 1001 → ℕ} {x : ℕ}
    {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    taoPrimeTupleEnlargedRemainderValue a ≤
      taoPrimeTupleEnlargedAmbientBound x P := by
  have haData := mem_taoPrimeTupleEnlargedRemainderPairs.mp ha
  have hm' := (mem_taoPrimeTupleSmoothRemainders.mp haData.1).1
  have hsupport := mem_taoPrimeTupleEnlargedSupport.mp haData.2
  have hzero := mem_taoDyadicPrimeBand.mp (hsupport 0)
  rw [taoPrimeTupleEnlargedScale_zero] at hzero
  have hzeroLe : a.2 0 ≤ 8 * P 0 := by omega
  have htail : taoPrimeTupleTailProduct a.2 ≤
      ∏ j ∈ (Finset.univ.erase (0 : Fin 1001)), 4 * P j := by
    unfold taoPrimeTupleTailProduct
    refine Finset.prod_le_prod' fun j hj => ?_
    have hj0 := (Finset.mem_erase.mp hj).1
    have hjData := mem_taoDyadicPrimeBand.mp (hsupport j)
    rw [taoPrimeTupleEnlargedScale_of_ne_zero P hj0] at hjData
    omega
  unfold taoPrimeTupleEnlargedRemainderValue taoPrimeTupleStart
  unfold taoPrimeTupleEnlargedAmbientBound
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hzeroLe 2) htail) hm'

/-- In an ordered scale tuple, every enlarged tail prime is strictly smaller
than the enlarged distinguished prime. -/
theorem taoPrimeTupleEnlarged_tail_lt_zero
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    {ω : TaoPrimeTuple} (hω : ω ∈ taoPrimeTupleEnlargedSupport P)
    {j : Fin 1001} (hj : j ≠ 0) :
    ω j < ω 0 := by
  have hjData := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hω) j)
  have hzeroData := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hω) 0)
  rw [taoPrimeTupleEnlargedScale_of_ne_zero P hj] at hjData
  rw [taoPrimeTupleEnlargedScale_zero] at hzeroData
  have hscale : P j ≤ P 0 := hPmono (Fin.zero_le j)
  omega

/-- Every prime factor of an admissible smooth remainder lies strictly below
the enlarged distinguished prime.  The assumption `2 ≤ P_last` removes the
only equality edge: `2P_last` is then composite. -/
theorem primeFactor_taoPrimeTupleSmoothRemainder_lt_enlarged_zero
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x m' q : ℕ} {ω : TaoPrimeTuple}
    (hm' : m' ∈ taoPrimeTupleSmoothRemainders x P)
    (hω : ω ∈ taoPrimeTupleEnlargedSupport P)
    (hq : Nat.Prime q) (hqm' : q ∣ m') :
    q < ω 0 := by
  have hsmooth := (mem_taoPrimeTupleSmoothRemainders.mp hm').2
  have hqCutoff := (isSmooth_iff.mp hsmooth).2 q hq hqm'
  have hlastZero : P (Fin.last 1000) ≤ P 0 :=
    hPmono (Fin.zero_le (Fin.last 1000))
  have hzeroData := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hω) 0)
  rw [taoPrimeTupleEnlargedScale_zero] at hzeroData
  have hstrict : q < 2 * P (Fin.last 1000) := by
    apply lt_of_le_of_ne hqCutoff
    intro heq
    have htwoDvd : 2 ∣ q := by
      rw [heq]
      exact dvd_mul_right 2 _
    rcases (Nat.dvd_prime hq).mp htwoDvd with htwoOne | htwoEq
    · norm_num at htwoOne
    · have hqTwo : q = 2 := htwoEq.symm
      have hcutoffTwo : 2 * P (Fin.last 1000) = 2 := by
        simpa only [hqTwo, taoPrimeTupleRemainderSmoothnessCutoff] using
          heq.symm
      omega
  omega

/-- The entire cofactor below the distinguished square is smooth at the
distinguished prime. -/
theorem isSmooth_taoPrimeTupleEnlargedCofactor
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    IsSmooth (taoPrimeTupleTailProduct a.2 * a.1) (a.2 0) := by
  have haData := mem_taoPrimeTupleEnlargedRemainderPairs.mp ha
  have hsupport := mem_taoPrimeTupleEnlargedSupport.mp haData.2
  rw [isSmooth_iff]
  constructor
  · apply mul_ne_zero
    · unfold taoPrimeTupleTailProduct
      exact Finset.prod_ne_zero_iff.mpr fun j hj =>
        (mem_taoDyadicPrimeBand.mp (hsupport j)).1.ne_zero
    · exact (isSmooth_iff.mp
        (mem_taoPrimeTupleSmoothRemainders.mp haData.1).2).1
  · intro q hq hqdiv
    rcases hq.dvd_mul.mp hqdiv with hqtail | hqm'
    · unfold taoPrimeTupleTailProduct at hqtail
      obtain ⟨j, hj, hqj⟩ :=
        (Prime.dvd_finsetProd_iff hq.prime a.2).mp hqtail
      have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
      have hjPrime := (mem_taoDyadicPrimeBand.mp (hsupport j)).1
      have hqeq : q = a.2 j :=
        (Nat.prime_dvd_prime_iff_eq hq hjPrime).mp hqj
      rw [hqeq]
      exact (taoPrimeTupleEnlarged_tail_lt_zero hPmono haData.2 hj0).le
    · exact (primeFactor_taoPrimeTupleSmoothRemainder_lt_enlarged_zero
        hPmono hlast haData.1 haData.2 hq hqm').le

/-- Every enlarged representation at ordered scales is a literal one-term
bad number. -/
theorem taoPrimeTupleEnlargedRemainderValue_mem_badOneTermSet
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000))
    {x : ℕ} {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleEnlargedRemainderPairs P x) :
    taoPrimeTupleEnlargedRemainderValue a ∈ badOneTermSet := by
  have hsupport := (mem_taoPrimeTupleEnlargedRemainderPairs.mp ha).2
  have hp := mem_taoDyadicPrimeBand.mp
    ((mem_taoPrimeTupleEnlargedSupport.mp hsupport) 0) |>.1
  apply mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
  refine ⟨a.2 0, taoPrimeTupleTailProduct a.2 * a.1, hp,
    isSmooth_taoPrimeTupleEnlargedCofactor hPmono hlast ha, ?_⟩
  simp only [taoPrimeTupleEnlargedRemainderValue, taoPrimeTupleStart]
  rw [Nat.mul_assoc]

/-- The image of an ordered enlarged family lies in the literal finite
one-term bad set at one absolute dilation of `x`. -/
theorem image_taoPrimeTupleEnlargedRemainderPairs_subset_badOneTermNumbersUpTo
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000)) (x : ℕ) :
    (taoPrimeTupleEnlargedRemainderPairs P x).image
        taoPrimeTupleEnlargedRemainderValue ⊆
      badOneTermNumbersUpTo (2 * taoPrimeTupleEnlargementFactor * x) := by
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨a, ha, rfl⟩ := hn
  rw [badOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩,
    taoPrimeTupleEnlargedRemainderValue_mem_badOneTermSet hPmono hlast ha⟩
  · have hsmooth := isSmooth_taoPrimeTupleEnlargedCofactor
      hPmono hlast ha
    have hp := mem_taoDyadicPrimeBand.mp
      ((mem_taoPrimeTupleEnlargedSupport.mp
        (mem_taoPrimeTupleEnlargedRemainderPairs.mp ha).2) 0) |>.1
    unfold taoPrimeTupleEnlargedRemainderValue taoPrimeTupleStart
    have hcofactor : 0 < taoPrimeTupleTailProduct a.2 * a.1 :=
      Nat.pos_of_ne_zero (isSmooth_iff.mp hsmooth).1
    rw [Nat.mul_assoc]
    exact Nat.mul_pos (pow_pos hp.pos 2) hcofactor
  · exact (taoPrimeTupleEnlargedRemainderValue_le_ambientBound ha).trans
      (taoPrimeTupleEnlargedAmbientBound_le_fixed_mul x P)

/-- Hence the number of distinct enlarged represented values is controlled
by the literal one-term count at an absolute multiple of `x`. -/
theorem card_image_taoPrimeTupleEnlargedRemainderPairs_le_badOneTermCount
    {P : Fin 1001 → ℕ} (hPmono : Antitone P)
    (hlast : 2 ≤ P (Fin.last 1000)) (x : ℕ) :
    ((taoPrimeTupleEnlargedRemainderPairs P x).image
        taoPrimeTupleEnlargedRemainderValue).card ≤
      badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) := by
  change ((taoPrimeTupleEnlargedRemainderPairs P x).image
      taoPrimeTupleEnlargedRemainderValue).card ≤
    (badOneTermNumbersUpTo (2 * taoPrimeTupleEnlargementFactor * x)).card
  exact Finset.card_le_card
    (image_taoPrimeTupleEnlargedRemainderPairs_subset_badOneTermNumbersUpTo
      hPmono hlast x)

end

end Tao2026
