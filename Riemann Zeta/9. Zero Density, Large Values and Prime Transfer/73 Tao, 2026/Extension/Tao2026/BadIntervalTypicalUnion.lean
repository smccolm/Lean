import Tao2026.BadIntervalTypicalWeighted

/-!
# Forward typical interval union

This module returns from the weighted prime-tuple family to literal normalized
bad intervals.  A canonical anatomy packet sends every forward-oriented
typical interval to its dyadic length, smooth remainder, and 1001-prime tuple.
The code remembers both the interval length and its left endpoint, so it is
injective.  The resulting interval union is therefore bounded by the global
length-weighted count.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

/-- Comparable-scale normalized intervals which are typical for the moving
slow cutoffs and whose distinguished squareful value is the left endpoint. -/
def taoForwardTypicalBadIntervalIndices
    (q : ℕ → ℕ) (x : ℕ) : Finset (ℕ × ℕ) :=
  (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    ∃ p₀ m : ℕ,
      IsForwardTypicalScaleNormalizedBadInterval x
        (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoPrimeTupleSlowUpperCutoff q x)
        NH.1 NH.2 p₀ (NH.1 + 1) m

theorem mem_taoForwardTypicalBadIntervalIndices
    {q : ℕ → ℕ} {x N H : ℕ} :
    (N, H) ∈ taoForwardTypicalBadIntervalIndices q x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        ∃ p₀ m : ℕ,
          IsForwardTypicalScaleNormalizedBadInterval x
            (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoPrimeTupleSlowUpperCutoff q x)
            N H p₀ (N + 1) m := by
  simp [taoForwardTypicalBadIntervalIndices]

/-- The literal union of the forward typical normalized intervals. -/
def taoForwardTypicalBadIntervalUnion
    (q : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (taoForwardTypicalBadIntervalIndices q x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

abbrev TaoForwardTypicalBadIntervalIndex (q : ℕ → ℕ) (x : ℕ) :=
  {NH : ℕ × ℕ // NH ∈ taoForwardTypicalBadIntervalIndices q x}

private theorem forwardTypicalIndex_exists_witness
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    ∃ p₀ m : ℕ,
      IsForwardTypicalScaleNormalizedBadInterval x
        (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoPrimeTupleSlowUpperCutoff q x)
        a.1.1 a.1.2 p₀ (a.1.1 + 1) m :=
  (mem_taoForwardTypicalBadIntervalIndices.mp a.2).2

def taoForwardTypicalIndexPrime
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) : ℕ :=
  Classical.choose (forwardTypicalIndex_exists_witness a)

def taoForwardTypicalIndexCofactor
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) : ℕ :=
  Classical.choose (Classical.choose_spec
    (forwardTypicalIndex_exists_witness a))

theorem taoForwardTypicalIndex_witness
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    IsForwardTypicalScaleNormalizedBadInterval x
      (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoPrimeTupleSlowUpperCutoff q x)
      a.1.1 a.1.2 (taoForwardTypicalIndexPrime a) (a.1.1 + 1)
      (taoForwardTypicalIndexCofactor a) :=
  Classical.choose_spec (Classical.choose_spec
    (forwardTypicalIndex_exists_witness a))

def TypicalPrimeAnatomy.mono_upper
    {lowerPrime upperPrime upperPrime' p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (hupper : upperPrime ≤ upperPrime') :
    TypicalPrimeAnatomy lowerPrime upperPrime' p₀ m where
  factors := a.factors
  remainder := a.remainder
  factors_prime := a.factors_prime
  factors_nonincreasing := a.factors_nonincreasing
  lower_le_last := a.lower_le_last
  first_le_p₀ := a.first_le_p₀
  p₀_le_upper := a.p₀_le_upper.trans hupper
  factorization := a.factorization
  remainder_smooth := a.remainder_smooth

theorem IsForwardTypicalScaleNormalizedBadInterval.mono_upper
    {x lengthCutoff squareThreshold lowerPrime upperPrime upperPrime'
      N H p₀ k m : ℕ}
    (htyp : IsForwardTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m)
    (hupper : upperPrime ≤ upperPrime') :
    IsForwardTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime' N H p₀ k m := by
  rcases htyp with
    ⟨⟨hnorm, hleft, hright, hshort, havoid, ⟨a⟩⟩, hforward⟩
  exact ⟨⟨hnorm, hleft, hright, hshort, havoid,
    ⟨a.mono_upper hupper⟩⟩, hforward⟩

def taoForwardTypicalIndexAnatomy
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    TypicalPrimeAnatomy
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoPrimeTupleSlowUpperCutoff q x)
      (taoForwardTypicalIndexPrime a)
      (taoForwardTypicalIndexCofactor a) :=
  Classical.choose
    (taoForwardTypicalIndex_witness a).1.exists_anatomy_with_remainder_bound

theorem taoForwardTypicalIndexAnatomy_remainder_le
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    (taoForwardTypicalIndexAnatomy a).remainder ≤
      2 * x /
        ((taoForwardTypicalIndexPrime a) ^ 2 *
          ∏ i, (taoForwardTypicalIndexAnatomy a).factors i) :=
  Classical.choose_spec
    (taoForwardTypicalIndex_witness a).1.exists_anatomy_with_remainder_bound

theorem taoPrimeTupleTailProduct_ofTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    taoPrimeTupleTailProduct (taoPrimeTupleOfTypicalAnatomy a) =
      ∏ i, a.factors i := by
  apply Nat.eq_of_mul_eq_mul_left hp₀.pos
  calc
    p₀ * taoPrimeTupleTailProduct (taoPrimeTupleOfTypicalAnatomy a) =
        (∏ j ∈ Finset.univ.erase (0 : Fin 1001),
          taoPrimeTupleOfTypicalAnatomy a j) * p₀ := by
      unfold taoPrimeTupleTailProduct
      rw [Nat.mul_comm]
    _ = ∏ j, taoPrimeTupleOfTypicalAnatomy a j := by
      simpa only [taoPrimeTupleOfTypicalAnatomy_zero] using
        Finset.prod_erase_mul Finset.univ
        (taoPrimeTupleOfTypicalAnatomy a)
        (Finset.mem_univ (0 : Fin 1001))
    _ = p₀ * ∏ i, a.factors i := by
      rw [Fin.prod_univ_succ]
      simp only [taoPrimeTupleOfTypicalAnatomy_zero,
        taoPrimeTupleOfTypicalAnatomy_succ]

theorem taoPrimeTupleStart_ofTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    taoPrimeTupleStart a.remainder (taoPrimeTupleOfTypicalAnatomy a) =
      p₀ ^ 2 * m := by
  calc
    taoPrimeTupleStart a.remainder (taoPrimeTupleOfTypicalAnatomy a) =
        p₀ ^ 2 * (∏ i, a.factors i) * a.remainder := by
      rw [taoPrimeTupleStart,
        taoPrimeTupleTailProduct_ofTypicalAnatomy hp₀,
        taoPrimeTupleOfTypicalAnatomy_zero]
    _ = p₀ ^ 2 * ((∏ i, a.factors i) * a.remainder) := by
      rw [Nat.mul_assoc]
    _ = p₀ ^ 2 * m :=
      congrArg (fun t => p₀ ^ 2 * t) a.factorization.symm

theorem prime_mem_taoDyadicPrimeBand_two_pow_natLog
    {p : ℕ} (hp : p.Prime) :
    p ∈ taoDyadicPrimeBand (2 ^ Nat.log 2 p) := by
  apply mem_taoDyadicPrimeBand.mpr
  refine ⟨hp, Nat.pow_log_le_self 2 hp.ne_zero, ?_⟩
  simpa only [pow_succ, mul_comm] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p)

theorem prime_taoPrimeTupleOfTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (j : Fin 1001) :
    (taoPrimeTupleOfTypicalAnatomy a j).Prime := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using hp₀
  · simpa using a.factors_prime i

theorem taoPrimeTupleOfTypicalAnatomy_mem_support
    {lowerPrime upperPrime p₀ m : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    taoPrimeTupleOfTypicalAnatomy a ∈
      taoPrimeTupleSupport
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) := by
  apply mem_taoPrimeTupleSupport.mpr
  intro j
  apply prime_mem_taoDyadicPrimeBand_two_pow_natLog
  exact prime_taoPrimeTupleOfTypicalAnatomy hp₀ a j

theorem taoPrimeTupleScaleDenominator_natLog_le_ofTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    taoPrimeTupleScaleDenominator
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) ≤
      p₀ ^ 2 * ∏ i, a.factors i := by
  calc
    taoPrimeTupleScaleDenominator
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) ≤
      (taoPrimeTupleOfTypicalAnatomy a 0) ^ 2 *
        ∏ j ∈ Finset.univ.erase (0 : Fin 1001),
          taoPrimeTupleOfTypicalAnatomy a j := by
      unfold taoPrimeTupleScaleDenominator
      gcongr with j hj
      · exact Nat.pow_log_le_self 2
          (by simpa using hp₀.ne_zero)
      · exact Nat.pow_log_le_self 2
          (prime_taoPrimeTupleOfTypicalAnatomy hp₀ a j).ne_zero
    _ = p₀ ^ 2 *
        taoPrimeTupleTailProduct (taoPrimeTupleOfTypicalAnatomy a) := by
      rw [taoPrimeTupleOfTypicalAnatomy_zero]
      rfl
    _ = p₀ ^ 2 * ∏ i, a.factors i := by
      rw [taoPrimeTupleTailProduct_ofTypicalAnatomy hp₀]

theorem typicalAnatomy_remainder_smooth_at_natLogScale
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    IsSmooth a.remainder
      (taoPrimeTupleRemainderSmoothnessCutoff
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j))) := by
  have hsmooth := a.remainder_smooth
  rw [isSmooth_iff] at hsmooth ⊢
  refine ⟨hsmooth.1, ?_⟩
  intro p hp hpdvd
  have hpLast := hsmooth.2 p hp hpdvd
  have hlast :
      a.factors (Fin.last 999) <
        2 * 2 ^ Nat.log 2 (a.factors (Fin.last 999)) := by
    simpa only [pow_succ, mul_comm] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
        (a.factors (Fin.last 999))
  have htupleLast :
      taoPrimeTupleOfTypicalAnatomy a (Fin.last 1000) =
        a.factors (Fin.last 999) := by
    rw [show Fin.last 1000 = (Fin.last 999).succ by rfl]
    exact taoPrimeTupleOfTypicalAnatomy_succ a (Fin.last 999)
  calc
    p ≤ a.factors (Fin.last 999) := hpLast
    _ ≤ 2 * 2 ^ Nat.log 2 (a.factors (Fin.last 999)) := hlast.le
    _ = taoPrimeTupleRemainderSmoothnessCutoff
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) := by
      rw [taoPrimeTupleRemainderSmoothnessCutoff, htupleLast]

theorem typicalAnatomy_remainder_mem_taoPrimeTupleSmoothRemainders
    {lowerPrime upperPrime p₀ m x : ℕ}
    (hp₀ : p₀.Prime)
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (hremainder :
      a.remainder ≤ 2 * x / (p₀ ^ 2 * ∏ i, a.factors i)) :
    a.remainder ∈ taoPrimeTupleSmoothRemainders x
      (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) := by
  apply mem_taoPrimeTupleSmoothRemainders.mpr
  constructor
  · refine hremainder.trans ?_
    apply Nat.div_le_div_left
    · exact taoPrimeTupleScaleDenominator_natLog_le_ofTypicalAnatomy hp₀ a
    · unfold taoPrimeTupleScaleDenominator
      positivity
  · exact typicalAnatomy_remainder_smooth_at_natLogScale a

theorem taoForwardTypicalIndexPrime_prime
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    (taoForwardTypicalIndexPrime a).Prime := by
  obtain ⟨_hHTwo, _hbad, hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    _hkm, _hendpoint, _hpow⟩ := (taoForwardTypicalIndex_witness a).1.1
  exact hp₀

/-- The canonical global tuple code attached to a forward typical interval. -/
def taoForwardTypicalIndexCode
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple :=
  let anatomy := taoForwardTypicalIndexAnatomy a
  ⟨fun j => Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j),
    Nat.log 2 a.1.2, anatomy.remainder,
    taoPrimeTupleOfTypicalAnatomy anatomy⟩

theorem taoForwardTypicalIndexCode_scale_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    (taoForwardTypicalIndexCode a).1 ∈
      taoPrimeTupleSlowOrderedScaleExponentTuples q x := by
  exact typicalAnatomy_natLog_mem_slowOrderedScaleExponentTuples
    (taoForwardTypicalIndexAnatomy a)

theorem taoForwardTypicalIndexCode_length_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    (taoForwardTypicalIndexCode a).2.1 ∈
      badIntervalTypicalDyadicExponents x := by
  have htyp := taoForwardTypicalIndex_witness a
  have hshort := htyp.1.2.2.2.1
  have hle : a.1.2 ≤ taoTypicalLengthCutoff x := hshort.le
  have hlogLe := Nat.log_mono_right (b := 2) hle
  simpa only [taoForwardTypicalIndexCode,
    badIntervalTypicalDyadicExponents, Finset.mem_range] using
      Nat.lt_succ_of_le hlogLe

theorem taoForwardTypicalIndexCode_start_eq
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    taoPrimeTupleStart (taoForwardTypicalIndexCode a).2.2.1
        (taoForwardTypicalIndexCode a).2.2.2 = a.1.1 + 1 := by
  let anatomy := taoForwardTypicalIndexAnatomy a
  have hp₀ := taoForwardTypicalIndexPrime_prime a
  have hstart := taoPrimeTupleStart_ofTypicalAnatomy hp₀ anatomy
  obtain ⟨_hHTwo, _hbad, _hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    hkm, _hendpoint, _hpow⟩ := (taoForwardTypicalIndex_witness a).1.1
  change taoPrimeTupleStart anatomy.remainder
    (taoPrimeTupleOfTypicalAnatomy anatomy) = a.1.1 + 1
  exact hstart.trans hkm.symm

theorem taoForwardTypicalIndexCode_length_eq
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x) :
    2 ^ (taoForwardTypicalIndexCode a).2.1 = a.1.2 := by
  obtain ⟨_hHTwo, _hbad, _hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    _hkm, _hendpoint, r, hr⟩ := (taoForwardTypicalIndex_witness a).1.1
  change 2 ^ Nat.log 2 a.1.2 = a.1.2
  rw [hr, Nat.log_pow (by norm_num : 1 < 2)]

theorem taoForwardTypicalIndexCode_pair_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x)
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoForwardTypicalIndexCode a).2.2 ∈
      taoPrimeTupleTypicalRemainderPairs
        (taoPrimeTupleDyadicScales (taoForwardTypicalIndexCode a).1) x
        (2 ^ (taoForwardTypicalIndexCode a).2.1)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) := by
  let anatomy := taoForwardTypicalIndexAnatomy a
  have hp₀ := taoForwardTypicalIndexPrime_prime a
  have hremainder : anatomy.remainder ∈
      taoPrimeTupleSmoothRemainders x
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j)) :=
    typicalAnatomy_remainder_mem_taoPrimeTupleSmoothRemainders hp₀ anatomy
      (taoForwardTypicalIndexAnatomy_remainder_le a)
  have hsupport : taoPrimeTupleOfTypicalAnatomy anatomy ∈
      taoPrimeTupleSupport
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j)) :=
    taoPrimeTupleOfTypicalAnatomy_mem_support hp₀ anatomy
  have htail :
      taoPrimeTupleTailProduct (taoPrimeTupleOfTypicalAnatomy anatomy) *
          anatomy.remainder = taoForwardTypicalIndexCofactor a := by
    rw [taoPrimeTupleTailProduct_ofTypicalAnatomy hp₀,
      ← anatomy.factorization]
  have hstart := taoForwardTypicalIndexCode_start_eq a
  have htypLarge :=
    (taoForwardTypicalIndex_witness a).mono_upper hupper
  have hevent :
      TaoPrimeTupleTypicalEvent x a.1.2
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) anatomy.remainder
        (taoPrimeTupleOfTypicalAnatomy anatomy) := by
    unfold TaoPrimeTupleTypicalEvent
    rw [show taoPrimeTupleStart anatomy.remainder
        (taoPrimeTupleOfTypicalAnatomy anatomy) = a.1.1 + 1 by
          simpa only [taoForwardTypicalIndexCode] using hstart,
      taoPrimeTupleOfTypicalAnatomy_zero, htail]
    simpa using htypLarge
  apply mem_taoPrimeTupleTypicalRemainderPairs.mpr
  change anatomy.remainder ∈ _ ∧ taoPrimeTupleOfTypicalAnatomy anatomy ∈ _
  refine ⟨hremainder, mem_taoPrimeTupleTypicalSupport.mpr ⟨hsupport, ?_⟩⟩
  simpa only [taoForwardTypicalIndexCode_length_eq a] using hevent

theorem taoForwardTypicalIndexCode_mem_global
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoForwardTypicalBadIntervalIndex q x)
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    taoForwardTypicalIndexCode a ∈
      taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x := by
  apply mem_taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples.mpr
  refine ⟨taoForwardTypicalIndexCode_scale_mem a, ?_⟩
  apply mem_taoPrimeTupleTypicalDyadicRemainderTriples.mpr
  exact ⟨taoForwardTypicalIndexCode_length_mem a,
    taoForwardTypicalIndexCode_pair_mem a hupper⟩

theorem taoForwardTypicalIndexCode_injOn
    (q : ℕ → ℕ) (x : ℕ) :
    Set.InjOn (@taoForwardTypicalIndexCode q x)
      (taoForwardTypicalBadIntervalIndices q x).attach := by
  intro a _ha b _hb hab
  apply Subtype.ext
  apply Prod.ext
  · have hstart := congrArg
      (fun z : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple =>
        taoPrimeTupleStart z.2.2.1 z.2.2.2) hab
    change taoPrimeTupleStart (taoForwardTypicalIndexCode a).2.2.1
        (taoForwardTypicalIndexCode a).2.2.2 =
      taoPrimeTupleStart (taoForwardTypicalIndexCode b).2.2.1
        (taoForwardTypicalIndexCode b).2.2.2 at hstart
    rw [taoForwardTypicalIndexCode_start_eq a,
      taoForwardTypicalIndexCode_start_eq b] at hstart
    omega
  · have hlength := congrArg
      (fun z : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple =>
        2 ^ z.2.1) hab
    change 2 ^ (taoForwardTypicalIndexCode a).2.1 =
      2 ^ (taoForwardTypicalIndexCode b).2.1 at hlength
    rw [taoForwardTypicalIndexCode_length_eq a,
      taoForwardTypicalIndexCode_length_eq b] at hlength
    exact hlength

theorem image_taoForwardTypicalIndexCode_subset_global
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoForwardTypicalBadIntervalIndices q x).attach.image
        (@taoForwardTypicalIndexCode q x) ⊆
      taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x := by
  intro z hz
  rw [Finset.mem_image] at hz
  obtain ⟨a, _ha, rfl⟩ := hz
  exact taoForwardTypicalIndexCode_mem_global a hupper

theorem sum_taoForwardTypicalBadIntervalLengths_le_globalWeight
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (∑ NH ∈ taoForwardTypicalBadIntervalIndices q x, NH.2) ≤
      taoPrimeTupleGlobalTypicalDyadicLengthWeight q x := by
  let S := (taoForwardTypicalBadIntervalIndices q x).attach
  let code := @taoForwardTypicalIndexCode q x
  calc
    (∑ NH ∈ taoForwardTypicalBadIntervalIndices q x, NH.2) =
        ∑ a ∈ S, a.1.2 := by
      simpa only [S] using
        (Finset.sum_attach (taoForwardTypicalBadIntervalIndices q x)
          (fun NH => NH.2)).symm
    _ = ∑ a ∈ S, 2 ^ (code a).2.1 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (taoForwardTypicalIndexCode_length_eq a).symm
    _ = ∑ z ∈ S.image code, 2 ^ z.2.1 := by
      symm
      exact Finset.sum_image (by
        simpa only [S, code] using
          taoForwardTypicalIndexCode_injOn q x)
    _ ≤ ∑ z ∈ taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x,
        2 ^ z.2.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by simpa only [S, code] using
          image_taoForwardTypicalIndexCode_subset_global hupper)
      intro z hz hnot
      positivity
    _ = taoPrimeTupleGlobalTypicalDyadicLengthWeight q x := rfl

theorem card_taoForwardTypicalBadIntervalUnion_le_globalWeight
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoForwardTypicalBadIntervalUnion q x).card ≤
      taoPrimeTupleGlobalTypicalDyadicLengthWeight q x := by
  calc
    (taoForwardTypicalBadIntervalUnion q x).card ≤
        ∑ NH ∈ taoForwardTypicalBadIntervalIndices q x,
          (consecutiveInterval NH.1 NH.2).card := by
      unfold taoForwardTypicalBadIntervalUnion
      exact Finset.card_biUnion_le
    _ = ∑ NH ∈ taoForwardTypicalBadIntervalIndices q x, NH.2 := by
      apply Finset.sum_congr rfl
      intro NH hNH
      simp [consecutiveInterval]
    _ ≤ taoPrimeTupleGlobalTypicalDyadicLengthWeight q x :=
      sum_taoForwardTypicalBadIntervalLengths_le_globalWeight hupper

/-- The moving upper anatomy cutoff is eventually below the fixed `z^1.01`
source margin used by Proposition 6.6. -/
theorem eventually_taoPrimeTupleSlowUpperCutoff_le_largePrimeSourceUpperCutoff
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleSlowUpperCutoff q x ≤
        taoLargePrimeSourceUpperCutoff x := by
  have hslow := tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq
  have hlarge :=
    tendsto_log_taoZPowerFloor_div_log_taoZ
      (show (0 : ℝ) < 101 / 100 by norm_num)
  have hlargeTop :
      Tendsto (taoZPowerFloor (101 / 100 : ℝ)) atTop atTop :=
    tendsto_taoZPowerFloor_atTop (by norm_num)
  filter_upwards
    [hslow.eventually
      (Iio_mem_nhds (show (1 : ℝ) < 201 / 200 by norm_num)),
     hlarge.eventually
      (Ioi_mem_nhds (show (201 / 200 : ℝ) < 101 / 100 by norm_num)),
     (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
     hlargeTop.eventually (eventually_ge_atTop (1 : ℕ))]
      with x hslowRatio hlargeRatio hlogZ hlargeOne
  have hslowPosNat : 0 < taoPrimeTupleSlowUpperCutoff q x := by
    unfold taoPrimeTupleSlowUpperCutoff taoOneTermExponentCutoff
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (taoZ_pos x) _)
  have hslowPos : (0 : ℝ) < taoPrimeTupleSlowUpperCutoff q x := by
    exact_mod_cast hslowPosNat
  have hlargePos : (0 : ℝ) < taoLargePrimeSourceUpperCutoff x := by
    exact_mod_cast hlargeOne
  have hratio :
      Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x) <
        Real.log (taoLargePrimeSourceUpperCutoff x) /
          Real.log (taoZ x) := by
    change Real.log (taoPrimeTupleSlowUpperCutoff q x) /
      Real.log (taoZ x) < 201 / 200 at hslowRatio
    change 201 / 200 < Real.log (taoLargePrimeSourceUpperCutoff x) /
      Real.log (taoZ x) at hlargeRatio
    exact hslowRatio.trans hlargeRatio
  have hlogs :
      Real.log (taoPrimeTupleSlowUpperCutoff q x) <
        Real.log (taoLargePrimeSourceUpperCutoff x) :=
    (div_lt_div_iff_of_pos_right hlogZ).mp hratio
  have hcast :
      (taoPrimeTupleSlowUpperCutoff q x : ℝ) <
        taoLargePrimeSourceUpperCutoff x :=
    (Real.strictMonoOn_log.lt_iff_lt hslowPos hlargePos).mp hlogs
  exact_mod_cast hcast.le

theorem eventually_card_taoForwardTypicalBadIntervalUnion_le_globalWeight
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ((taoForwardTypicalBadIntervalUnion q x).card : ℝ) ≤
        (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) := by
  filter_upwards
    [eventually_taoPrimeTupleSlowUpperCutoff_le_largePrimeSourceUpperCutoff hq]
      with x hupper
  exact_mod_cast
    card_taoForwardTypicalBadIntervalUnion_le_globalWeight hupper

/-- Conditional on the explicit Burgess input, the literal forward typical
interval union is negligible relative to the dilated one-term count. -/
theorem card_taoForwardTypicalBadIntervalUnion_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ => ((taoForwardTypicalBadIntervalUnion q x).card : ℝ))
      =o[atTop]
    (fun x : ℕ =>
      (badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  have hweight :=
    taoPrimeTupleGlobalTypicalLengthWeight_isLittleO_dilatedBadOneTermCount
      hC hburgess hq
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards
    [eventually_card_taoForwardTypicalBadIntervalUnion_le_globalWeight hq,
     hweight.bound hε] with x hcard hbound
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (taoForwardTypicalBadIntervalUnion q x).card),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ taoPrimeTupleGlobalTypicalDyadicLengthWeight q x),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))] at hbound ⊢
  exact hcard.trans hbound

/-! ## Exact orientation split -/

/-- The right-endpoint counterpart of the source's named forward predicate. -/
def IsBackwardTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
    lowerPrime upperPrime N H p₀ k m ∧ k = N + H

/-- All typical comparable-scale normalized intervals at the moving cutoffs,
before choosing an endpoint orientation. -/
def taoTypicalBadIntervalIndices
    (q : ℕ → ℕ) (x : ℕ) : Finset (ℕ × ℕ) :=
  (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    ∃ p₀ k m : ℕ,
      IsTypicalScaleNormalizedBadInterval x
        (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoPrimeTupleSlowUpperCutoff q x)
        NH.1 NH.2 p₀ k m

theorem mem_taoTypicalBadIntervalIndices
    {q : ℕ → ℕ} {x N H : ℕ} :
    (N, H) ∈ taoTypicalBadIntervalIndices q x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        ∃ p₀ k m : ℕ,
          IsTypicalScaleNormalizedBadInterval x
            (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoPrimeTupleSlowUpperCutoff q x)
            N H p₀ k m := by
  simp [taoTypicalBadIntervalIndices]

/-- The still-separate right-endpoint family.  Its probability estimate uses
the source's symmetric `v-l` anti-sieve rather than the compiled `v+l` one. -/
def taoBackwardTypicalBadIntervalIndices
    (q : ℕ → ℕ) (x : ℕ) : Finset (ℕ × ℕ) :=
  (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    ∃ p₀ m : ℕ,
      IsBackwardTypicalScaleNormalizedBadInterval x
        (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoPrimeTupleSlowUpperCutoff q x)
        NH.1 NH.2 p₀ (NH.1 + NH.2) m

theorem mem_taoBackwardTypicalBadIntervalIndices
    {q : ℕ → ℕ} {x N H : ℕ} :
    (N, H) ∈ taoBackwardTypicalBadIntervalIndices q x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        ∃ p₀ m : ℕ,
          IsBackwardTypicalScaleNormalizedBadInterval x
            (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoPrimeTupleSlowUpperCutoff q x)
            N H p₀ (N + H) m := by
  simp [taoBackwardTypicalBadIntervalIndices]

def taoTypicalBadIntervalUnion
    (q : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (taoTypicalBadIntervalIndices q x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

def taoBackwardTypicalBadIntervalUnion
    (q : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (taoBackwardTypicalBadIntervalIndices q x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem taoTypicalBadIntervalIndices_subset_forward_union_backward
    (q : ℕ → ℕ) (x : ℕ) :
    taoTypicalBadIntervalIndices q x ⊆
      taoForwardTypicalBadIntervalIndices q x ∪
        taoBackwardTypicalBadIntervalIndices q x := by
  intro NH hNH
  obtain ⟨hscale, p₀, k, m, htyp⟩ :=
    mem_taoTypicalBadIntervalIndices.mp hNH
  rcases htyp.1.2.2.2.2.2.2.2.2.1 with hforward | hbackward
  · apply Finset.mem_union_left
    apply mem_taoForwardTypicalBadIntervalIndices.mpr
    subst k
    exact ⟨hscale, p₀, m, htyp, rfl⟩
  · apply Finset.mem_union_right
    apply mem_taoBackwardTypicalBadIntervalIndices.mpr
    subst k
    exact ⟨hscale, p₀, m, htyp, rfl⟩

theorem taoTypicalBadIntervalUnion_subset_forward_union_backward
    (q : ℕ → ℕ) (x : ℕ) :
    taoTypicalBadIntervalUnion q x ⊆
      taoForwardTypicalBadIntervalUnion q x ∪
        taoBackwardTypicalBadIntervalUnion q x := by
  intro n hn
  rw [taoTypicalBadIntervalUnion, Finset.mem_biUnion] at hn
  obtain ⟨NH, hNH, hnInterval⟩ := hn
  have horientation :=
    taoTypicalBadIntervalIndices_subset_forward_union_backward q x hNH
  rw [Finset.mem_union] at horientation
  rcases horientation with hforward | hbackward
  · apply Finset.mem_union_left
    rw [taoForwardTypicalBadIntervalUnion, Finset.mem_biUnion]
    exact ⟨NH, hforward, hnInterval⟩
  · apply Finset.mem_union_right
    rw [taoBackwardTypicalBadIntervalUnion, Finset.mem_biUnion]
    exact ⟨NH, hbackward, hnInterval⟩

end

end Tao2026
