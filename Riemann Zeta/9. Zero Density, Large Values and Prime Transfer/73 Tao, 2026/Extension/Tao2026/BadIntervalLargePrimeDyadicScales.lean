import Tao2026.BadIntervalLargePrimeAdaptiveComplete
import Tao2026.BadIntervalLongSum

/-!
# Source dyadic scales for the large-prime moment estimates

The source prime range is cut off between `z^0.01` and `z^1.01`.  We retain
exactly the powers of two whose half-open dyadic bands can meet that range.
This module proves exact coverage, a logarithmic scale count, and the fixed
power margins needed by the adaptive block theorems.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

/-- The lower endpoint of the source large-prime range. -/
def taoLargePrimeSourceLowerCutoff (x : ℕ) : ℕ :=
  taoZPowerFloor (1 / 100 : ℝ) x

/-- A fixed upper margin for the source range `p ≤ z^(1+o(1))`. -/
def taoLargePrimeSourceUpperCutoff (x : ℕ) : ℕ :=
  taoZPowerFloor (101 / 100 : ℝ) x

/-- Dyadic exponents whose bands can meet the source large-prime range. -/
def taoLargePrimeSourceDyadicExponents (x : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (taoLargePrimeSourceUpperCutoff x) + 1)).filter
    fun r => taoLargePrimeSourceLowerCutoff x < 2 ^ (r + 1)

/-- The literal finite source large-prime range. -/
def taoLargePrimeSourcePrimes (x : ℕ) : Finset ℕ :=
  (Finset.Ioc (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x)).filter Nat.Prime

/-- The part of the literal source prime range lying in one dyadic band. -/
def taoLargePrimeSourceDyadicPrimeSlice (x r : ℕ) : Finset ℕ :=
  taoDyadicPrimeBand (2 ^ r) ∩ taoLargePrimeSourcePrimes x

/-- Shift-prime indices in one exact source dyadic slice. -/
def taoLargePrimeSourceDyadicIndices (x r H : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 H).product (taoLargePrimeSourceDyadicPrimeSlice x r)

theorem mem_taoLargePrimeSourceDyadicExponents {x r : ℕ} :
    r ∈ taoLargePrimeSourceDyadicExponents x ↔
      r ≤ Nat.log 2 (taoLargePrimeSourceUpperCutoff x) ∧
      taoLargePrimeSourceLowerCutoff x < 2 ^ (r + 1) := by
  simp [taoLargePrimeSourceDyadicExponents]

theorem mem_taoLargePrimeSourcePrimes {x p : ℕ} :
    p ∈ taoLargePrimeSourcePrimes x ↔
      Nat.Prime p ∧ taoLargePrimeSourceLowerCutoff x < p ∧
        p ≤ taoLargePrimeSourceUpperCutoff x := by
  simp only [taoLargePrimeSourcePrimes, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem taoLargeAntiSievePrimeRange_sourceCutoffs_eq (x : ℕ) :
    taoLargeAntiSievePrimeRange (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) =
      taoLargePrimeSourcePrimes x := by
  rfl

theorem taoLargeAntiSieveIndices_sourceCutoffs_eq (x H : ℕ) :
    taoLargeAntiSieveIndices (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) H =
      (Finset.Ico 1 H).product (taoLargePrimeSourcePrimes x) := by
  rfl

/-- Every source prime belongs to the dyadic band selected by its base-two
logarithm, and that exponent occurs in the source grid. -/
theorem sourcePrime_mem_sourceDyadicBand
    {x p : ℕ} (hp : p ∈ taoLargePrimeSourcePrimes x) :
    Nat.log 2 p ∈ taoLargePrimeSourceDyadicExponents x ∧
      p ∈ taoDyadicPrimeBand (2 ^ Nat.log 2 p) := by
  have hpData := mem_taoLargePrimeSourcePrimes.mp hp
  have hpPos : 0 < p := hpData.1.pos
  have hpLower : taoLargePrimeSourceLowerCutoff x < p := hpData.2.1
  have hpUpper : p ≤ taoLargePrimeSourceUpperCutoff x := hpData.2.2
  have hlogUpper : Nat.log 2 p ≤
      Nat.log 2 (taoLargePrimeSourceUpperCutoff x) :=
    Nat.log_mono_right hpUpper
  have hpBandUpper : p < 2 ^ (Nat.log 2 p + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  constructor
  · exact mem_taoLargePrimeSourceDyadicExponents.mpr
      ⟨hlogUpper, hpLower.trans hpBandUpper⟩
  · exact mem_taoDyadicPrimeBand.mpr
      ⟨hpData.1, Nat.pow_log_le_self 2 hpPos.ne', by
        simpa only [pow_succ, mul_comm] using hpBandUpper⟩

/-- The literal source prime range is covered by the union of the retained
dyadic prime bands. -/
theorem taoLargePrimeSourcePrimes_subset_dyadicUnion (x : ℕ) :
    taoLargePrimeSourcePrimes x ⊆
      (taoLargePrimeSourceDyadicExponents x).biUnion fun r =>
        taoDyadicPrimeBand (2 ^ r) := by
  intro p hp
  have hpData := sourcePrime_mem_sourceDyadicBand hp
  exact Finset.mem_biUnion.mpr ⟨Nat.log 2 p, hpData.1, hpData.2⟩

theorem taoLargePrimeSourceDyadicPrimeSlice_subset_band (x r : ℕ) :
    taoLargePrimeSourceDyadicPrimeSlice x r ⊆ taoDyadicPrimeBand (2 ^ r) := by
  exact Finset.inter_subset_left

/-- Distinct powers of two define disjoint half-open dyadic prime bands. -/
theorem disjoint_taoDyadicPrimeBand_two_pow {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (taoDyadicPrimeBand (2 ^ r)) (taoDyadicPrimeBand (2 ^ s)) := by
  apply Finset.disjoint_left.mpr
  intro p hpr hps
  have hrData := mem_taoDyadicPrimeBand.mp hpr
  have hsData := mem_taoDyadicPrimeBand.mp hps
  rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
  · have hpow : 2 ^ (r + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpUpper : p < 2 ^ (r + 1) := by
      simpa only [pow_succ, mul_comm] using hrData.2.2
    omega
  · have hpow : 2 ^ (s + 1) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpUpper : p < 2 ^ (s + 1) := by
      simpa only [pow_succ, mul_comm] using hsData.2.2
    omega

theorem disjoint_taoLargePrimeSourceDyadicPrimeSlice
    {x r s : ℕ} (hrs : r ≠ s) :
    Disjoint (taoLargePrimeSourceDyadicPrimeSlice x r)
      (taoLargePrimeSourceDyadicPrimeSlice x s) := by
  exact (disjoint_taoDyadicPrimeBand_two_pow hrs).mono
    (taoLargePrimeSourceDyadicPrimeSlice_subset_band x r)
    (taoLargePrimeSourceDyadicPrimeSlice_subset_band x s)

/-- The exact source prime range is the disjoint union of its retained
dyadic slices. -/
theorem biUnion_taoLargePrimeSourceDyadicPrimeSlice (x : ℕ) :
    (taoLargePrimeSourceDyadicExponents x).biUnion
        (taoLargePrimeSourceDyadicPrimeSlice x) =
      taoLargePrimeSourcePrimes x := by
  ext p
  constructor
  · intro hp
    obtain ⟨r, hr, hpSlice⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpSlice).2
  · intro hp
    have hpBand := sourcePrime_mem_sourceDyadicBand hp
    exact Finset.mem_biUnion.mpr
      ⟨Nat.log 2 p, hpBand.1, Finset.mem_inter.mpr ⟨hpBand.2, hp⟩⟩

/-- Exact summation over the disjoint source prime slices. -/
theorem sum_taoLargePrimeSourcePrimes_eq_sum_dyadicSlices
    (x : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ taoLargePrimeSourcePrimes x, f p) =
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ p ∈ taoLargePrimeSourceDyadicPrimeSlice x r, f p := by
  rw [← biUnion_taoLargePrimeSourceDyadicPrimeSlice x]
  apply Finset.sum_biUnion
  intro r hr s hs hrs
  exact disjoint_taoLargePrimeSourceDyadicPrimeSlice hrs

/-- The source shift-prime index set is the disjoint union of its dyadic
index slices. -/
theorem biUnion_taoLargePrimeSourceDyadicIndices (x H : ℕ) :
    (taoLargePrimeSourceDyadicExponents x).biUnion
        (fun r => taoLargePrimeSourceDyadicIndices x r H) =
      (Finset.Ico 1 H).product (taoLargePrimeSourcePrimes x) := by
  ext a
  constructor
  · intro ha
    obtain ⟨r, hr, haSlice⟩ := Finset.mem_biUnion.mp ha
    have haData := Finset.mem_product.mp haSlice
    apply Finset.mem_product.mpr
    refine ⟨haData.1, ?_⟩
    rw [← biUnion_taoLargePrimeSourceDyadicPrimeSlice x]
    exact Finset.mem_biUnion.mpr ⟨r, hr, haData.2⟩
  · intro ha
    have haData := Finset.mem_product.mp ha
    have haPrime := haData.2
    rw [← biUnion_taoLargePrimeSourceDyadicPrimeSlice x] at haPrime
    obtain ⟨r, hr, haSlice⟩ := Finset.mem_biUnion.mp haPrime
    apply Finset.mem_biUnion.mpr
    exact ⟨r, hr, Finset.mem_product.mpr ⟨haData.1, haSlice⟩⟩

theorem disjoint_taoLargePrimeSourceDyadicIndices
    {x H r s : ℕ} (hrs : r ≠ s) :
    Disjoint (taoLargePrimeSourceDyadicIndices x r H)
      (taoLargePrimeSourceDyadicIndices x s H) := by
  apply Finset.disjoint_left.mpr
  intro a har has
  have harData := Finset.mem_product.mp har
  have hasData := Finset.mem_product.mp has
  exact Finset.disjoint_left.mp
    (disjoint_taoLargePrimeSourceDyadicPrimeSlice hrs)
      harData.2 hasData.2

/-- Exact summation over the disjoint source shift-prime slices. -/
theorem sum_taoLargePrimeSourceIndices_eq_sum_dyadicSlices
    (x H : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ a ∈ (Finset.Ico 1 H).product (taoLargePrimeSourcePrimes x), f a) =
      ∑ r ∈ taoLargePrimeSourceDyadicExponents x,
        ∑ a ∈ taoLargePrimeSourceDyadicIndices x r H, f a := by
  rw [← biUnion_taoLargePrimeSourceDyadicIndices x H]
  apply Finset.sum_biUnion
  intro r hr s hs hrs
  exact disjoint_taoLargePrimeSourceDyadicIndices hrs

/-- The grid has at most the ambient base-two logarithmic count. -/
theorem card_taoLargePrimeSourceDyadicExponents_le (x : ℕ) :
    (taoLargePrimeSourceDyadicExponents x).card ≤
      Nat.log 2 (taoLargePrimeSourceUpperCutoff x) + 1 := by
  unfold taoLargePrimeSourceDyadicExponents
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The fixed upper cutoff eventually lies strictly beyond the lower one. -/
theorem eventually_taoLargePrimeSourceLowerCutoff_lt_upperCutoff :
    ∀ᶠ x : ℕ in atTop,
      taoLargePrimeSourceLowerCutoff x < taoLargePrimeSourceUpperCutoff x := by
  filter_upwards
    [tendsto_taoZ_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x hz
  have hzpos : 0 < taoZ x := taoZ_pos x
  have hsmallOne : (1 : ℝ) ≤ (taoZ x) ^ (1 / 100 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hsmallNonneg : (0 : ℝ) ≤ (taoZ x) ^ (1 / 100 : ℝ) :=
    Real.rpow_nonneg hzpos.le _
  have hlower : (taoLargePrimeSourceLowerCutoff x : ℝ) ≤
      (taoZ x) ^ (1 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hzpos.le _)
  have hupperLt : (taoZ x) ^ (101 / 100 : ℝ) <
      (taoLargePrimeSourceUpperCutoff x : ℝ) + 1 := by
    simpa only [taoLargePrimeSourceUpperCutoff, taoZPowerFloor] using
      Nat.lt_floor_add_one ((taoZ x) ^ (101 / 100 : ℝ))
  have hpower : (taoZ x) ^ (101 / 100 : ℝ) =
      (taoZ x) ^ (1 / 100 : ℝ) * taoZ x := by
    calc
      (taoZ x) ^ (101 / 100 : ℝ) =
          (taoZ x) ^ ((1 / 100 : ℝ) + 1) := by norm_num
      _ = (taoZ x) ^ (1 / 100 : ℝ) * (taoZ x) ^ (1 : ℝ) := by
        rw [Real.rpow_add hzpos]
      _ = (taoZ x) ^ (1 / 100 : ℝ) * taoZ x := by
        rw [Real.rpow_one]
  rw [hpower] at hupperLt
  have hcast : (taoLargePrimeSourceLowerCutoff x : ℝ) <
      taoLargePrimeSourceUpperCutoff x := by
    nlinarith [mul_le_mul_of_nonneg_left hz hsmallNonneg]
  exact_mod_cast hcast

/-- The source dyadic grid is eventually nonempty. -/
theorem eventually_taoLargePrimeSourceDyadicExponents_nonempty :
    ∀ᶠ x : ℕ in atTop,
      (taoLargePrimeSourceDyadicExponents x).Nonempty := by
  filter_upwards
    [eventually_taoLargePrimeSourceLowerCutoff_lt_upperCutoff] with x hcut
  have hupperPos : 0 < taoLargePrimeSourceUpperCutoff x :=
    lt_of_le_of_lt (Nat.zero_le _) hcut
  let r := Nat.log 2 (taoLargePrimeSourceUpperCutoff x)
  have hupperBand : taoLargePrimeSourceUpperCutoff x < 2 ^ (r + 1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
  exact ⟨r, mem_taoLargePrimeSourceDyadicExponents.mpr
    ⟨le_rfl, hcut.trans hupperBand⟩⟩

/-- A small fixed power of `z` lies below the floored `z^0.01` cutoff after
allowing the factor two lost at the bottom of a dyadic band. -/
theorem eventually_two_mul_taoZ_rpow_one_two_hundred_le_sourceLowerCutoff :
    ∀ᶠ x : ℕ in atTop,
      2 * (taoZ x) ^ (1 / 200 : ℝ) ≤
        (taoLargePrimeSourceLowerCutoff x : ℝ) := by
  have ht : Tendsto (fun x : ℕ =>
      (taoZ x) ^ (1 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_taoZ_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (3 : ℝ))] with x hx
  let t : ℝ := (taoZ x) ^ (1 / 200 : ℝ)
  have htNonneg : 0 ≤ t := by dsimp only [t]; positivity
  have hpower : (taoZ x) ^ (1 / 100 : ℝ) = t ^ (2 : ℕ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (taoZ_pos x).le]
    congr 1
    norm_num
  have hfloorLt : (taoZ x) ^ (1 / 100 : ℝ) <
      (taoLargePrimeSourceLowerCutoff x : ℝ) + 1 := by
    simpa only [taoLargePrimeSourceLowerCutoff, taoZPowerFloor] using
      Nat.lt_floor_add_one ((taoZ x) ^ (1 / 100 : ℝ))
  rw [hpower] at hfloorLt
  dsimp only [t] at hx htNonneg ⊢
  nlinarith

/-- Every retained scale has the fixed lower and upper source margins used
by the adaptive Burgess block estimates. -/
theorem eventually_taoLargePrimeSourceDyadicScale_bounds :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      (taoZ x) ^ (1 / 200 : ℝ) ≤ (2 ^ r : ℕ) ∧
      ((2 ^ r : ℕ) : ℝ) ≤ (taoZ x) ^ (101 / 100 : ℝ) ∧
      2 ≤ (2 ^ r : ℕ) := by
  have hzTwo : ∀ᶠ x : ℕ in atTop,
      (2 : ℝ) ≤ (taoZ x) ^ (1 / 200 : ℝ) := by
    exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      tendsto_taoZ_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards
    [eventually_two_mul_taoZ_rpow_one_two_hundred_le_sourceLowerCutoff,
      hzTwo] with x hlower hzTwoX
  intro r hr
  have hrData := mem_taoLargePrimeSourceDyadicExponents.mp hr
  have hlowerTwoReal : (2 : ℝ) ≤
      (taoLargePrimeSourceLowerCutoff x : ℝ) := by
    nlinarith
  have hlowerTwoNat : 2 ≤ taoLargePrimeSourceLowerCutoff x := by
    exact_mod_cast hlowerTwoReal
  have hupperNe : taoLargePrimeSourceUpperCutoff x ≠ 0 := by
    intro hzero
    have hrzero : r = 0 := by
      simpa [hzero] using hrData.1
    subst r
    norm_num at hrData
    omega
  have hscaleUpperNat : 2 ^ r ≤ taoLargePrimeSourceUpperCutoff x := by
    calc
      2 ^ r ≤ 2 ^ Nat.log 2 (taoLargePrimeSourceUpperCutoff x) :=
        Nat.pow_le_pow_right (by norm_num) hrData.1
      _ ≤ taoLargePrimeSourceUpperCutoff x :=
        Nat.pow_log_le_self 2 hupperNe
  have hupperFloor : (taoLargePrimeSourceUpperCutoff x : ℝ) ≤
      (taoZ x) ^ (101 / 100 : ℝ) := by
    exact Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
  have hscaleUpper : ((2 ^ r : ℕ) : ℝ) ≤
      (taoZ x) ^ (101 / 100 : ℝ) := by
    have hscaleUpperCast : ((2 ^ r : ℕ) : ℝ) ≤
        (taoLargePrimeSourceUpperCutoff x : ℝ) := by
      exact_mod_cast hscaleUpperNat
    exact hscaleUpperCast.trans hupperFloor
  have hbandMeet : (taoLargePrimeSourceLowerCutoff x : ℝ) <
      2 * ((2 ^ r : ℕ) : ℝ) := by
    have hbandMeetNat : taoLargePrimeSourceLowerCutoff x < 2 * 2 ^ r := by
      simpa only [pow_succ, mul_comm] using hrData.2
    exact_mod_cast hbandMeetNat
  have hscaleLower : (taoZ x) ^ (1 / 200 : ℝ) ≤
      ((2 ^ r : ℕ) : ℝ) := by
    nlinarith
  have htwoNat : 2 ≤ (2 ^ r : ℕ) := by
    exact_mod_cast hzTwoX.trans hscaleLower
  exact ⟨hscaleLower, hscaleUpper, htwoNat⟩

/-- Any selector taking values in the source dyadic grid is a valid adaptive
source-band selector. -/
theorem taoLargePrimeDyadicBandSelector_of_eventually_mem_sourceDyadicExponents
    {r : ℕ → ℕ}
    (hr : ∀ᶠ x : ℕ in atTop,
      r x ∈ taoLargePrimeSourceDyadicExponents x) :
    TaoLargePrimeDyadicBandSelector (fun x => 2 ^ r x) := by
  have hb := eventually_taoLargePrimeSourceDyadicScale_bounds
  have hz : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ taoZ x :=
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop 1)
  refine
    { lower := (hb.and hr).mono fun x hx => (hx.1 (r x) hx.2).1
      upper := ((hb.and hr).and hz).mono fun x hx =>
        ((hx.1.1 (r x) hx.1.2).2.1).trans
          (Real.rpow_le_rpow_of_exponent_le hx.2 (by norm_num))
      upper_source := (hb.and hr).mono fun x hx => (hx.1 (r x) hx.2).2.1 }

/-- The source shift cutoff lies below every retained dyadic scale. -/
theorem eventually_taoTypicalLengthCutoff_le_sourceDyadicScale_sub_one :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoLargePrimeSourceDyadicExponents x,
      taoTypicalLengthCutoff x ≤ 2 ^ r - 1 := by
  filter_upwards
    [eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
      (C := (2 : ℝ)) (δ := (1 / 200 : ℝ)) (by norm_num) (by norm_num),
      eventually_taoLargePrimeSourceDyadicScale_bounds] with x hH hb
  intro r hr
  have hscale := hb r hr
  have htwice : 2 * taoTypicalLengthCutoff x ≤ 2 ^ r := by
    exact_mod_cast hH.trans hscale.1
  omega

/-- The number of retained scales is at most four logarithms of `z`. -/
theorem eventually_card_taoLargePrimeSourceDyadicExponents_cast_le_log :
    ∀ᶠ x : ℕ in atTop,
      ((taoLargePrimeSourceDyadicExponents x).card : ℝ) ≤
        4 * Real.log (taoZ x) := by
  filter_upwards
    [tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1)),
      (tendsto_taoZPowerFloor_atTop
        (by norm_num : (0 : ℝ) < 101 / 100)).eventually
          (eventually_ge_atTop (1 : ℕ))] with x hz hupperPos
  have hcardNat := card_taoLargePrimeSourceDyadicExponents_le x
  have hcard : ((taoLargePrimeSourceDyadicExponents x).card : ℝ) ≤
      (Nat.log 2 (taoLargePrimeSourceUpperCutoff x) : ℝ) + 1 := by
    exact_mod_cast hcardNat
  have hnatLog := badInterval_natLogTwo_cast_le_log_div hupperPos
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hupperFloor : (taoLargePrimeSourceUpperCutoff x : ℝ) ≤
      (taoZ x) ^ (101 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
  have hupperRealPos : (0 : ℝ) < taoLargePrimeSourceUpperCutoff x := by
    exact_mod_cast hupperPos
  have hlogUpper : Real.log (taoLargePrimeSourceUpperCutoff x) ≤
      (101 / 100 : ℝ) * Real.log (taoZ x) := by
    calc
      Real.log (taoLargePrimeSourceUpperCutoff x) ≤
          Real.log ((taoZ x) ^ (101 / 100 : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hupperRealPos
          (Real.rpow_pos_of_pos (taoZ_pos x) _)
          hupperFloor
      _ = (101 / 100 : ℝ) * Real.log (taoZ x) := by
        rw [Real.log_rpow (taoZ_pos x)]
  have hlogZOne : (1 : ℝ) ≤ Real.log (taoZ x) := by
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hz
  have hlogUpperNonneg : 0 ≤
      Real.log (taoLargePrimeSourceUpperCutoff x) :=
    Real.log_nonneg (by exact_mod_cast hupperPos)
  have hnatLog' : (Nat.log 2 (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
      2 * Real.log (taoLargePrimeSourceUpperCutoff x) := by
    calc
      (Nat.log 2 (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
          Real.log (taoLargePrimeSourceUpperCutoff x) / Real.log 2 := hnatLog
      _ ≤ 2 * Real.log (taoLargePrimeSourceUpperCutoff x) := by
        apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
        nlinarith
  calc
    ((taoLargePrimeSourceDyadicExponents x).card : ℝ) ≤
        (Nat.log 2 (taoLargePrimeSourceUpperCutoff x) : ℝ) + 1 := hcard
    _ ≤ 2 * Real.log (taoLargePrimeSourceUpperCutoff x) + 1 := by
      linarith
    _ ≤ 2 * ((101 / 100 : ℝ) * Real.log (taoZ x)) + 1 := by
      linarith
    _ ≤ 4 * Real.log (taoZ x) := by
      nlinarith

end

end Tao2026
