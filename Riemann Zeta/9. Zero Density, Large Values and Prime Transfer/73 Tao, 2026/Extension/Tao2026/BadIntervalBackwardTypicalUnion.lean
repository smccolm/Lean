import Tao2026.BadIntervalBackwardTypicalWeighted

/-!
# Backward typical interval union

This module returns from the reflected weighted prime-tuple family to literal
right-endpoint normalized bad intervals.  The canonical code records the
right endpoint `N + H` and the dyadic length `H`; together these recover the
original interval and make the code injective.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

abbrev TaoBackwardTypicalBadIntervalIndex (q : ℕ → ℕ) (x : ℕ) :=
  {NH : ℕ × ℕ // NH ∈ taoBackwardTypicalBadIntervalIndices q x}

private theorem backwardTypicalIndex_exists_witness
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    ∃ p₀ m : ℕ,
      IsBackwardTypicalScaleNormalizedBadInterval x
        (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoPrimeTupleSlowUpperCutoff q x)
        a.1.1 a.1.2 p₀ (a.1.1 + a.1.2) m :=
  (mem_taoBackwardTypicalBadIntervalIndices.mp a.2).2

def taoBackwardTypicalIndexPrime
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) : ℕ :=
  Classical.choose (backwardTypicalIndex_exists_witness a)

def taoBackwardTypicalIndexCofactor
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) : ℕ :=
  Classical.choose (Classical.choose_spec
    (backwardTypicalIndex_exists_witness a))

theorem taoBackwardTypicalIndex_witness
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    IsBackwardTypicalScaleNormalizedBadInterval x
      (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoPrimeTupleSlowUpperCutoff q x)
      a.1.1 a.1.2 (taoBackwardTypicalIndexPrime a) (a.1.1 + a.1.2)
      (taoBackwardTypicalIndexCofactor a) :=
  Classical.choose_spec (Classical.choose_spec
    (backwardTypicalIndex_exists_witness a))

theorem IsBackwardTypicalScaleNormalizedBadInterval.mono_upper
    {x lengthCutoff squareThreshold lowerPrime upperPrime upperPrime'
      N H p₀ k m : ℕ}
    (htyp : IsBackwardTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m)
    (hupper : upperPrime ≤ upperPrime') :
    IsBackwardTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime' N H p₀ k m := by
  rcases htyp with
    ⟨⟨hnorm, hleft, hright, hshort, havoid, ⟨a⟩⟩, hbackward⟩
  exact ⟨⟨hnorm, hleft, hright, hshort, havoid,
    ⟨a.mono_upper hupper⟩⟩, hbackward⟩

def taoBackwardTypicalIndexAnatomy
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    TypicalPrimeAnatomy
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoPrimeTupleSlowUpperCutoff q x)
      (taoBackwardTypicalIndexPrime a)
      (taoBackwardTypicalIndexCofactor a) :=
  Classical.choose
    (taoBackwardTypicalIndex_witness a).1.exists_anatomy_with_remainder_bound

theorem taoBackwardTypicalIndexAnatomy_remainder_le
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    (taoBackwardTypicalIndexAnatomy a).remainder ≤
      2 * x /
        ((taoBackwardTypicalIndexPrime a) ^ 2 *
          ∏ i, (taoBackwardTypicalIndexAnatomy a).factors i) :=
  Classical.choose_spec
    (taoBackwardTypicalIndex_witness a).1.exists_anatomy_with_remainder_bound

theorem taoBackwardTypicalIndexPrime_prime
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    (taoBackwardTypicalIndexPrime a).Prime := by
  obtain ⟨_hHTwo, _hbad, hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    _hkm, _hendpoint, _hpow⟩ := (taoBackwardTypicalIndex_witness a).1.1
  exact hp₀

/-- The canonical global tuple code attached to a backward typical interval. -/
def taoBackwardTypicalIndexCode
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple :=
  let anatomy := taoBackwardTypicalIndexAnatomy a
  ⟨fun j => Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j),
    Nat.log 2 a.1.2, anatomy.remainder,
    taoPrimeTupleOfTypicalAnatomy anatomy⟩

theorem taoBackwardTypicalIndexCode_scale_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    (taoBackwardTypicalIndexCode a).1 ∈
      taoPrimeTupleSlowOrderedScaleExponentTuples q x := by
  exact typicalAnatomy_natLog_mem_slowOrderedScaleExponentTuples
    (taoBackwardTypicalIndexAnatomy a)

theorem taoBackwardTypicalIndexCode_length_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    (taoBackwardTypicalIndexCode a).2.1 ∈
      badIntervalTypicalDyadicExponents x := by
  have htyp := taoBackwardTypicalIndex_witness a
  have hshort := htyp.1.2.2.2.1
  have hle : a.1.2 ≤ taoTypicalLengthCutoff x := hshort.le
  have hlogLe := Nat.log_mono_right (b := 2) hle
  simpa only [taoBackwardTypicalIndexCode,
    badIntervalTypicalDyadicExponents, Finset.mem_range] using
      Nat.lt_succ_of_le hlogLe

theorem taoBackwardTypicalIndexCode_start_eq
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    taoPrimeTupleStart (taoBackwardTypicalIndexCode a).2.2.1
        (taoBackwardTypicalIndexCode a).2.2.2 = a.1.1 + a.1.2 := by
  let anatomy := taoBackwardTypicalIndexAnatomy a
  have hp₀ := taoBackwardTypicalIndexPrime_prime a
  have hstart := taoPrimeTupleStart_ofTypicalAnatomy hp₀ anatomy
  obtain ⟨_hHTwo, _hbad, _hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    hkm, _hendpoint, _hpow⟩ := (taoBackwardTypicalIndex_witness a).1.1
  change taoPrimeTupleStart anatomy.remainder
    (taoPrimeTupleOfTypicalAnatomy anatomy) = a.1.1 + a.1.2
  exact hstart.trans hkm.symm

theorem taoBackwardTypicalIndexCode_length_eq
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x) :
    2 ^ (taoBackwardTypicalIndexCode a).2.1 = a.1.2 := by
  obtain ⟨_hHTwo, _hbad, _hp₀, _hHltp, _hpMax, _hk, _hmSmooth,
    _hkm, _hendpoint, r, hr⟩ := (taoBackwardTypicalIndex_witness a).1.1
  change 2 ^ Nat.log 2 a.1.2 = a.1.2
  rw [hr, Nat.log_pow (by norm_num : 1 < 2)]

theorem taoBackwardTypicalIndexCode_pair_mem
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x)
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoBackwardTypicalIndexCode a).2.2 ∈
      taoPrimeTupleBackwardTypicalRemainderPairs
        (taoPrimeTupleDyadicScales (taoBackwardTypicalIndexCode a).1) x
        (2 ^ (taoBackwardTypicalIndexCode a).2.1)
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) := by
  let anatomy := taoBackwardTypicalIndexAnatomy a
  have hp₀ := taoBackwardTypicalIndexPrime_prime a
  have hremainder : anatomy.remainder ∈
      taoPrimeTupleSmoothRemainders x
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j)) :=
    typicalAnatomy_remainder_mem_taoPrimeTupleSmoothRemainders hp₀ anatomy
      (taoBackwardTypicalIndexAnatomy_remainder_le a)
  have hsupport : taoPrimeTupleOfTypicalAnatomy anatomy ∈
      taoPrimeTupleSupport
        (fun j => 2 ^ Nat.log 2 (taoPrimeTupleOfTypicalAnatomy anatomy j)) :=
    taoPrimeTupleOfTypicalAnatomy_mem_support hp₀ anatomy
  have htail :
      taoPrimeTupleTailProduct (taoPrimeTupleOfTypicalAnatomy anatomy) *
          anatomy.remainder = taoBackwardTypicalIndexCofactor a := by
    rw [taoPrimeTupleTailProduct_ofTypicalAnatomy hp₀,
      ← anatomy.factorization]
  have hstart := taoBackwardTypicalIndexCode_start_eq a
  have htypLarge :=
    (taoBackwardTypicalIndex_witness a).mono_upper hupper
  have hevent :
      TaoPrimeTupleBackwardTypicalEvent x a.1.2
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) anatomy.remainder
        (taoPrimeTupleOfTypicalAnatomy anatomy) := by
    unfold TaoPrimeTupleBackwardTypicalEvent
    rw [show taoPrimeTupleStart anatomy.remainder
        (taoPrimeTupleOfTypicalAnatomy anatomy) = a.1.1 + a.1.2 by
          simpa only [taoBackwardTypicalIndexCode] using hstart,
      taoPrimeTupleOfTypicalAnatomy_zero, htail]
    simpa using htypLarge
  apply mem_taoPrimeTupleBackwardTypicalRemainderPairs.mpr
  change anatomy.remainder ∈ _ ∧ taoPrimeTupleOfTypicalAnatomy anatomy ∈ _
  refine ⟨hremainder,
    mem_taoPrimeTupleBackwardTypicalSupport.mpr ⟨hsupport, ?_⟩⟩
  simpa only [taoBackwardTypicalIndexCode_length_eq a] using hevent

theorem taoBackwardTypicalIndexCode_mem_global
    {q : ℕ → ℕ} {x : ℕ}
    (a : TaoBackwardTypicalBadIntervalIndex q x)
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    taoBackwardTypicalIndexCode a ∈
      taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples q x := by
  apply mem_taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples.mpr
  refine ⟨taoBackwardTypicalIndexCode_scale_mem a, ?_⟩
  apply mem_taoPrimeTupleBackwardTypicalDyadicRemainderTriples.mpr
  exact ⟨taoBackwardTypicalIndexCode_length_mem a,
    taoBackwardTypicalIndexCode_pair_mem a hupper⟩

theorem taoBackwardTypicalIndexCode_injOn
    (q : ℕ → ℕ) (x : ℕ) :
    Set.InjOn (@taoBackwardTypicalIndexCode q x)
      (taoBackwardTypicalBadIntervalIndices q x).attach := by
  intro a _ha b _hb hab
  apply Subtype.ext
  apply Prod.ext
  · have hstart := congrArg
      (fun z : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple =>
        taoPrimeTupleStart z.2.2.1 z.2.2.2) hab
    change taoPrimeTupleStart (taoBackwardTypicalIndexCode a).2.2.1
        (taoBackwardTypicalIndexCode a).2.2.2 =
      taoPrimeTupleStart (taoBackwardTypicalIndexCode b).2.2.1
        (taoBackwardTypicalIndexCode b).2.2.2 at hstart
    rw [taoBackwardTypicalIndexCode_start_eq a,
      taoBackwardTypicalIndexCode_start_eq b] at hstart
    have hlength := congrArg
      (fun z : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple =>
        2 ^ z.2.1) hab
    change 2 ^ (taoBackwardTypicalIndexCode a).2.1 =
      2 ^ (taoBackwardTypicalIndexCode b).2.1 at hlength
    rw [taoBackwardTypicalIndexCode_length_eq a,
      taoBackwardTypicalIndexCode_length_eq b] at hlength
    omega
  · have hlength := congrArg
      (fun z : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple =>
        2 ^ z.2.1) hab
    change 2 ^ (taoBackwardTypicalIndexCode a).2.1 =
      2 ^ (taoBackwardTypicalIndexCode b).2.1 at hlength
    rw [taoBackwardTypicalIndexCode_length_eq a,
      taoBackwardTypicalIndexCode_length_eq b] at hlength
    exact hlength

theorem image_taoBackwardTypicalIndexCode_subset_global
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoBackwardTypicalBadIntervalIndices q x).attach.image
        (@taoBackwardTypicalIndexCode q x) ⊆
      taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples q x := by
  intro z hz
  rw [Finset.mem_image] at hz
  obtain ⟨a, _ha, rfl⟩ := hz
  exact taoBackwardTypicalIndexCode_mem_global a hupper

theorem sum_taoBackwardTypicalBadIntervalLengths_le_globalWeight
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (∑ NH ∈ taoBackwardTypicalBadIntervalIndices q x, NH.2) ≤
      taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x := by
  let S := (taoBackwardTypicalBadIntervalIndices q x).attach
  let code := @taoBackwardTypicalIndexCode q x
  calc
    (∑ NH ∈ taoBackwardTypicalBadIntervalIndices q x, NH.2) =
        ∑ a ∈ S, a.1.2 := by
      simpa only [S] using
        (Finset.sum_attach (taoBackwardTypicalBadIntervalIndices q x)
          (fun NH => NH.2)).symm
    _ = ∑ a ∈ S, 2 ^ (code a).2.1 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (taoBackwardTypicalIndexCode_length_eq a).symm
    _ = ∑ z ∈ S.image code, 2 ^ z.2.1 := by
      symm
      exact Finset.sum_image (by
        simpa only [S, code] using
          taoBackwardTypicalIndexCode_injOn q x)
    _ ≤ ∑ z ∈ taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples q x,
        2 ^ z.2.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by simpa only [S, code] using
          image_taoBackwardTypicalIndexCode_subset_global hupper)
      intro z hz hnot
      positivity
    _ = taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x := rfl

theorem card_taoBackwardTypicalBadIntervalUnion_le_globalWeight
    {q : ℕ → ℕ} {x : ℕ}
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≤
      taoLargePrimeSourceUpperCutoff x) :
    (taoBackwardTypicalBadIntervalUnion q x).card ≤
      taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x := by
  calc
    (taoBackwardTypicalBadIntervalUnion q x).card ≤
        ∑ NH ∈ taoBackwardTypicalBadIntervalIndices q x,
          (consecutiveInterval NH.1 NH.2).card := by
      unfold taoBackwardTypicalBadIntervalUnion
      exact Finset.card_biUnion_le
    _ = ∑ NH ∈ taoBackwardTypicalBadIntervalIndices q x, NH.2 := by
      apply Finset.sum_congr rfl
      intro NH hNH
      simp [consecutiveInterval]
    _ ≤ taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x :=
      sum_taoBackwardTypicalBadIntervalLengths_le_globalWeight hupper

theorem eventually_card_taoBackwardTypicalBadIntervalUnion_le_globalWeight
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ((taoBackwardTypicalBadIntervalUnion q x).card : ℝ) ≤
        (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) := by
  filter_upwards
    [eventually_taoPrimeTupleSlowUpperCutoff_le_largePrimeSourceUpperCutoff hq]
      with x hupper
  exact_mod_cast
    card_taoBackwardTypicalBadIntervalUnion_le_globalWeight hupper

/-- Conditional on the explicit Burgess input, the literal backward typical
interval union is negligible relative to the dilated one-term count. -/
theorem card_taoBackwardTypicalBadIntervalUnion_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ => ((taoBackwardTypicalBadIntervalUnion q x).card : ℝ))
      =o[atTop]
    (fun x : ℕ =>
      (badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  have hweight :=
    taoPrimeTupleGlobalBackwardTypicalLengthWeight_isLittleO_dilatedBadOneTermCount
      hC hburgess hq
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards
    [eventually_card_taoBackwardTypicalBadIntervalUnion_le_globalWeight hq,
     hweight.bound hε] with x hcard hbound
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (taoBackwardTypicalBadIntervalUnion q x).card),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))] at hbound ⊢
  exact hcard.trans hbound

/-- Both endpoint orientations together are negligible relative to the same
dilated one-term count. -/
theorem card_taoTypicalBadIntervalUnion_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ => ((taoTypicalBadIntervalUnion q x).card : ℝ))
      =o[atTop]
    (fun x : ℕ =>
      (badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  have hforward :=
    card_taoForwardTypicalBadIntervalUnion_isLittleO_dilatedBadOneTermCount
      hC hburgess hq
  have hbackward :=
    card_taoBackwardTypicalBadIntervalUnion_isLittleO_dilatedBadOneTermCount
      hC hburgess hq
  have hsum := hforward.add hbackward
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hsum.bound hε] with x hbound
  have hsubset :=
    taoTypicalBadIntervalUnion_subset_forward_union_backward q x
  have hcardNat :
    (taoTypicalBadIntervalUnion q x).card ≤
        (taoForwardTypicalBadIntervalUnion q x).card +
          (taoBackwardTypicalBadIntervalUnion q x).card :=
    (Finset.card_le_card hsubset).trans
      (Finset.card_union_le
        (taoForwardTypicalBadIntervalUnion q x)
        (taoBackwardTypicalBadIntervalUnion q x))
  have hcard :
      ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
        (taoForwardTypicalBadIntervalUnion q x).card +
          (taoBackwardTypicalBadIntervalUnion q x).card := by
    exact_mod_cast hcardNat
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (taoTypicalBadIntervalUnion q x).card),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (taoForwardTypicalBadIntervalUnion q x).card +
        (taoBackwardTypicalBadIntervalUnion q x).card),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))] at hbound ⊢
  exact hcard.trans hbound

/-- Quantitative two-orientation form: the full typical interval union keeps
the source logarithmic saving relative to the fixed dilated one-term count. -/
theorem eventually_card_taoTypicalBadIntervalUnion_le_logSaving_mul_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
        (2 * (100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
            8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)) *
          (1000 : ℝ) ^ (1000 : ℕ)) *
            ((badOneTermCount
                (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) /
              Real.log x ^ (1 - ε)) := by
  let F : ℕ → ℝ := fun x =>
    taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x
  let D : ℕ → ℝ := fun x =>
    (badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)
  let M : ℝ := (1000 : ℝ) ^ (1000 : ℕ)
  let K : ℝ :=
    100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
      8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  have hM : 0 ≤ M := by
    exact pow_nonneg (by norm_num) _
  filter_upwards
    [eventually_card_taoForwardTypicalBadIntervalUnion_le_globalWeight hq,
     eventually_card_taoBackwardTypicalBadIntervalUnion_le_globalWeight hq,
     eventually_taoPrimeTupleGlobalTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
      hC hburgess hq,
     eventually_taoPrimeTupleGlobalBackwardTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
      hC hburgess hq,
     eventually_taoPrimeTupleTypicalWeightedAssemblyFactor_le_logSaving
      hC hburgess hε,
     (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (0 : ℝ))]
      with x hforwardCard hbackwardCard hforwardWeight hbackwardWeight
        hfactor hlog
  have hsubset :=
    taoTypicalBadIntervalUnion_subset_forward_union_backward q x
  have hcardNat :
      (taoTypicalBadIntervalUnion q x).card ≤
        (taoForwardTypicalBadIntervalUnion q x).card +
          (taoBackwardTypicalBadIntervalUnion q x).card :=
    (Finset.card_le_card hsubset).trans
      (Finset.card_union_le
        (taoForwardTypicalBadIntervalUnion q x)
        (taoBackwardTypicalBadIntervalUnion q x))
  have hcard :
      ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
        (taoForwardTypicalBadIntervalUnion q x).card +
          (taoBackwardTypicalBadIntervalUnion q x).card := by
    exact_mod_cast hcardNat
  have hforward :
      ((taoForwardTypicalBadIntervalUnion q x).card : ℝ) ≤
        F x * (D x * M) := by
    calc
      ((taoForwardTypicalBadIntervalUnion q x).card : ℝ) ≤
          (taoPrimeTupleGlobalTypicalDyadicLengthWeight q x : ℝ) :=
        hforwardCard
      _ ≤ F x * (D x * M) := by
        simpa only [F, D, M, Nat.cast_mul, Nat.cast_pow] using hforwardWeight
  have hbackward :
      ((taoBackwardTypicalBadIntervalUnion q x).card : ℝ) ≤
        F x * (D x * M) := by
    calc
      ((taoBackwardTypicalBadIntervalUnion q x).card : ℝ) ≤
          (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) :=
        hbackwardCard
      _ ≤ F x * (D x * M) := by
        simpa only [F, D, M, Nat.cast_mul, Nat.cast_pow] using hbackwardWeight
  have hfactor' : F x ≤ K / Real.log x ^ (1 - ε) := by
    simpa only [F, K] using hfactor
  have hdenPos : 0 < Real.log x ^ (1 - ε) :=
    Real.rpow_pos_of_pos hlog _
  change ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
    (2 * K * M) * (D x / Real.log x ^ (1 - ε))
  calc
    ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
        (taoForwardTypicalBadIntervalUnion q x).card +
          (taoBackwardTypicalBadIntervalUnion q x).card := hcard
    _ ≤ F x * (D x * M) + F x * (D x * M) :=
      add_le_add hforward hbackward
    _ = 2 * (F x * (D x * M)) := (two_mul _).symm
    _ = 2 * F x * (D x * M) :=
      (mul_assoc 2 (F x) (D x * M)).symm
    _ ≤ 2 * (K / Real.log x ^ (1 - ε)) * (D x * M) := by
      gcongr
    _ = (2 * K * M) * (D x / Real.log x ^ (1 - ε)) := by
      field_simp [hdenPos.ne']

end

end Tao2026
