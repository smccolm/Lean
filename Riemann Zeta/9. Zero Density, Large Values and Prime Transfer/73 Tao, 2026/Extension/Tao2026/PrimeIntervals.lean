import GafniTao.ExceptionalDensity
import GafniTao.LocalCover
import GafniTao.CountableDiagonal
import Mathlib.NumberTheory.Bertrand

/-!
# Quantitative prime-interval input

This module exposes the fixed-power estimate that is actually needed for
Tao's Proposition 2.3(iii).  The density-zero corollary alone is too weak for
the later double-counting argument, so the bridge returns one exponent below
one that works for every fixed positive discrepancy threshold.
-/

open Filter MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt Topology

namespace Tao2026

noncomputable section

/-- Tao Proposition 2.3(i), with the paper's endpoint orientation
`N / 2 < p ≤ N`. -/
theorem taoProposition23i {N : ℕ} (hN : 2 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ N / 2 < p ∧ p ≤ N := by
  have hhalf : N / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hpLower, hpUpper⟩ := Nat.bertrand (N / 2) hhalf
  exact ⟨p, hp, hpLower, hpUpper.trans (by omega)⟩

/-- The literal endpoint set in Tao's Proposition 2.3(iii): the interval
length is determined by the outer scale `X`, and the closed interval
`[x', x' + X^theta]` contains no natural prime.  The countable-intersection
representation makes measurability part of the definition's usable API. -/
def primeFreeEndpointSet (X theta : ℝ) : Set ℝ :=
  Icc 0 X ∩ ⋂ p : ℕ,
    if p.Prime then (Icc ((p : ℝ) - X ^ theta) (p : ℝ))ᶜ else Set.univ

/-- Membership in `primeFreeEndpointSet` is exactly Tao's closed-interval
prime-free condition, including both endpoints. -/
theorem mem_primeFreeEndpointSet {X theta x : ℝ} :
    x ∈ primeFreeEndpointSet X theta ↔
      0 ≤ x ∧ x ≤ X ∧
        ∀ p : ℕ, p.Prime → ¬(x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x + X ^ theta) := by
  constructor
  · intro hx
    rw [primeFreeEndpointSet, Set.mem_inter_iff] at hx
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    intro p hp hbetween
    have hpOutside := Set.mem_iInter.mp hx.2 p
    simp only [hp, if_true, Set.mem_compl_iff, Set.mem_Icc] at hpOutside
    apply hpOutside
    constructor <;> linarith
  · rintro ⟨hxZero, hxX, hfree⟩
    rw [primeFreeEndpointSet, Set.mem_inter_iff]
    refine ⟨⟨hxZero, hxX⟩, Set.mem_iInter.mpr ?_⟩
    intro p
    by_cases hp : p.Prime
    · simp only [hp, if_true, Set.mem_compl_iff, Set.mem_Icc]
      intro hpInterval
      exact hfree p hp ⟨hpInterval.2, by linarith [hpInterval.1]⟩
    · simp [hp]

theorem measurableSet_primeFreeEndpointSet (X theta : ℝ) :
    MeasurableSet (primeFreeEndpointSet X theta) := by
  rw [primeFreeEndpointSet]
  refine measurableSet_Icc.inter (MeasurableSet.iInter fun p => ?_)
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact measurableSet_Icc.compl
  · simp [hp]

/-- Lebesgue measure of Tao's literal constant-length prime-free endpoint
set on `[0,X]`. -/
noncomputable def primeFreeEndpointMeasure (X theta : ℝ) : ℝ :=
  (volume (primeFreeEndpointSet X theta)).toReal

/-- The prime-supported part of the Mangoldt sum vanishes on a closed
prime-free interval.  This is the endpoint-sensitive bridge needed before
the higher-prime-power tail is estimated. -/
theorem primeMangoldtIntervalSum_eq_zero_of_primeFree
    {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hfree : ∀ p : ℕ, p.Prime →
      ¬(a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a + y)) :
    GafniTao.primeMangoldtIntervalSum a y = 0 := by
  classical
  unfold GafniTao.primeMangoldtIntervalSum
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpInterval := (GafniTao.mem_mangoldtInterval ha hy p).mp hp.1
  exact (hfree p hp.2 ⟨hpInterval.1.le, hpInterval.2⟩).elim

theorem primePowerTailIntervalSum_nonneg (a y : ℝ) :
    0 ≤ GafniTao.primePowerTailIntervalSum a y := by
  unfold GafniTao.primePowerTailIntervalSum
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- The exact higher-prime-power tail on `(x, x+x^theta]` is bounded by the
prime-power part of Gafni--Tao's already audited little-o envelope. -/
theorem primePowerTailIntervalSum_le_remainderEnvelope
    {x theta : ℝ} (hx : 3 ≤ x) (hthetaUpper : theta ≤ 1) :
    GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤
      GafniTao.localReplacementRemainderEnvelope theta 1 x := by
  have hxOne : 1 ≤ x := by linarith
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hpowNonneg : 0 ≤ x ^ theta := Real.rpow_nonneg hxPos.le theta
  have hpowLe : x ^ theta ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxOne hthetaUpper
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogXNonneg : 0 ≤ Real.log x := Real.log_nonneg hxOne
  have hlogTwoLe : Real.log 2 ≤ Real.log x := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hxPos (by linarith)
  have hlogSumNonneg : 0 ≤ Real.log (x + x ^ theta) :=
    Real.log_nonneg (hxOne.trans (le_add_of_nonneg_right hpowNonneg))
  have hlogSum : Real.log (x + x ^ theta) ≤ 2 * Real.log x := by
    calc
      Real.log (x + x ^ theta) ≤ Real.log (2 * x) := by
        apply Real.log_le_log (by positivity)
        linarith
      _ = Real.log 2 + Real.log x := by
        rw [Real.log_mul (by norm_num) hxPos.ne']
      _ ≤ 2 * Real.log x := by linarith
  have hfloor :
      (⌊Real.log (x + x ^ theta) / Real.log 2⌋₊ : ℝ) ≤
        2 * Real.log x / Real.log 2 := by
    calc
      (⌊Real.log (x + x ^ theta) / Real.log 2⌋₊ : ℝ) ≤
          Real.log (x + x ^ theta) / Real.log 2 :=
        Nat.floor_le (div_nonneg hlogSumNonneg hlogTwo.le)
      _ ≤ 2 * Real.log x / Real.log 2 := by gcongr
  have hpowerIdentity : x ^ (-(1 / 2 : ℝ)) * x ^ theta =
      x ^ (theta - 1 / 2) := by
    rw [← Real.rpow_add hxPos]
    congr 1
    ring_nf
  have htail := GafniTao.primePowerTailIntervalSum_le hxOne hpowNonneg
  calc
    GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤
        (⌊Real.log (x + x ^ theta) / Real.log 2⌋₊ : ℝ) *
          ((x ^ (-(1 / 2 : ℝ)) * x ^ theta + 1) *
            Real.log (x + x ^ theta)) := htail
    _ ≤ (2 * Real.log x / Real.log 2) *
          ((x ^ (theta - 1 / 2) + 1) * (2 * Real.log x)) := by
        rw [hpowerIdentity]
        gcongr
    _ = (4 / Real.log 2) * (1 * x ^ (theta - 1 / 2) + 1) *
          Real.log x ^ 2 := by ring_nf
    _ ≤ GafniTao.localReplacementRemainderEnvelope theta 1 x := by
      unfold GafniTao.localReplacementRemainderEnvelope
      have hfirst : 0 ≤
          324 * 3 ^ (theta / 4) * x ^ (theta / 4) * Real.log x ^ 4 := by
        positivity
      linarith

/-- Uniformly at large endpoints, all higher prime powers contribute at most
half of the physical short-interval length. -/
theorem eventually_primePowerTailIntervalSum_le_half
    {theta : ℝ} (htheta : 0 < theta) (hthetaUpper : theta ≤ 1) :
    ∀ᶠ x : ℝ in atTop,
      GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤
        (1 / 2 : ℝ) * x ^ theta := by
  have hsmall :=
    (GafniTao.localReplacementRemainderEnvelope_isLittleO
      (u := 1) htheta).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall, eventually_ge_atTop (3 : ℝ)] with x hbound hx
  have hxNonneg : 0 ≤ x := by linarith
  calc
    GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤
        GafniTao.localReplacementRemainderEnvelope theta 1 x :=
      primePowerTailIntervalSum_le_remainderEnvelope hx hthetaUpper
    _ ≤ |GafniTao.localReplacementRemainderEnvelope theta 1 x| := le_abs_self _
    _ ≤ (1 / 2 : ℝ) * |x ^ theta| := hbound
    _ = (1 / 2 : ℝ) * x ^ theta := by
      rw [abs_of_nonneg (Real.rpow_nonneg hxNonneg theta)]

/-- On a prime-free interval, the complete Mangoldt sum is exactly its
higher-prime-power tail; prime powers are retained, not silently discarded. -/
theorem mangoldtIntervalSum_eq_primePowerTail_of_primeFree
    {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hfree : ∀ p : ℕ, p.Prime →
      ¬(a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a + y)) :
    GafniTao.mangoldtIntervalSum a y =
      GafniTao.primePowerTailIntervalSum a y := by
  rw [GafniTao.mangoldtIntervalSum_eq_prime_add_tail,
    primeMangoldtIntervalSum_eq_zero_of_primeFree ha hy hfree, zero_add]

/-- Once the prime-power tail is at most half the interval length, a
prime-free short interval lies in Gafni--Tao's discrepancy exceptional set at
threshold `1/2`. -/
theorem mem_shortIntervalExceptionalSet_half_of_primeFree
    {X a theta : ℝ} (haShell : a ∈ Icc X (2 * X)) (ha : 0 ≤ a)
    (hfree : ∀ p : ℕ, p.Prime →
      ¬(a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a + a ^ theta))
    (htail : GafniTao.primePowerTailIntervalSum a (a ^ theta) ≤
      (1 / 2 : ℝ) * a ^ theta) :
    a ∈ GafniTao.shortIntervalExceptionalSet (1 / 2) X theta := by
  refine ⟨haShell, ?_⟩
  have hpow : 0 ≤ a ^ theta := Real.rpow_nonneg ha theta
  have hsum : GafniTao.mangoldtShortSum a theta =
      GafniTao.primePowerTailIntervalSum a (a ^ theta) := by
    exact mangoldtIntervalSum_eq_primePowerTail_of_primeFree ha hpow hfree
  have htailLe : GafniTao.primePowerTailIntervalSum a (a ^ theta) ≤ a ^ theta := by
    linarith
  rw [GafniTao.shortIntervalDiscrepancy, hsum, abs_of_nonpos (sub_nonpos.mpr htailLe)]
  linarith

/-- The dyadic variable-length prime-free set used to connect Tao's literal
constant-length endpoint set to Gafni--Tao's exceptional set. -/
def dyadicPrimeFreeShortSet (X theta : ℝ) : Set ℝ :=
  Icc X (2 * X) ∩ ⋂ p : ℕ,
    if p.Prime then
      ({x : ℝ | x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ theta})ᶜ
    else Set.univ

theorem mem_dyadicPrimeFreeShortSet {X theta x : ℝ} :
    x ∈ dyadicPrimeFreeShortSet X theta ↔
      x ∈ Icc X (2 * X) ∧
        ∀ p : ℕ, p.Prime →
          ¬(x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ theta) := by
  constructor
  · intro hx
    rw [dyadicPrimeFreeShortSet, Set.mem_inter_iff] at hx
    refine ⟨hx.1, ?_⟩
    intro p hp hbetween
    have hpOutside := Set.mem_iInter.mp hx.2 p
    simp only [hp, if_true, Set.mem_compl_iff, Set.mem_setOf_eq] at hpOutside
    exact hpOutside hbetween
  · rintro ⟨hxShell, hfree⟩
    rw [dyadicPrimeFreeShortSet, Set.mem_inter_iff]
    refine ⟨hxShell, Set.mem_iInter.mpr ?_⟩
    intro p
    by_cases hp : p.Prime
    · simp only [hp, if_true, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact hfree p hp
    · simp [hp]

theorem measurableSet_dyadicPrimeFreeShortSet
    {X theta : ℝ} (htheta : 0 ≤ theta) :
    MeasurableSet (dyadicPrimeFreeShortSet X theta) := by
  rw [dyadicPrimeFreeShortSet]
  refine measurableSet_Icc.inter (MeasurableSet.iInter fun p => ?_)
  by_cases hp : p.Prime
  · rw [if_pos hp]
    apply MeasurableSet.compl
    exact (measurableSet_le measurable_id measurable_const).inter
      (measurableSet_le measurable_const
        (measurable_id.add (Real.continuous_rpow_const htheta).measurable))
  · simp [hp]

theorem dyadicPrimeFreeShortSet_subset_Icc (X theta : ℝ) :
    dyadicPrimeFreeShortSet X theta ⊆ Icc X (2 * X) := by
  intro x hx
  exact (mem_dyadicPrimeFreeShortSet.mp hx).1

/-- Lebesgue measure of the dyadic variable-length prime-free endpoint set. -/
noncomputable def dyadicPrimeFreeMeasure (X theta : ℝ) : ℝ :=
  (volume (dyadicPrimeFreeShortSet X theta)).toReal

theorem dyadicPrimeFreeMeasure_le_scale
    {X theta : ℝ} (hX : 0 ≤ X) :
    dyadicPrimeFreeMeasure X theta ≤ X := by
  have hIccFinite : volume (Icc X (2 * X)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  change volume.real (dyadicPrimeFreeShortSet X theta) ≤ X
  calc
    volume.real (dyadicPrimeFreeShortSet X theta) ≤
        volume.real (Icc X (2 * X)) :=
      measureReal_mono (dyadicPrimeFreeShortSet_subset_Icc X theta) hIccFinite.ne
    _ = X := by
      change (volume (Icc X (2 * X))).toReal = X
      rw [Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring_nf

/-- An eventual fixed-power estimate becomes a uniform estimate on all
positive dyadic scales.  The finitely many pre-threshold scales are absorbed
using their interval length. -/
theorem uniform_dyadicPrimeFreeMeasure_bound_of_fixedPower
    {theta xi : ℝ} (hxi : 0 < xi)
    (hbound : GafniTao.FixedPowerBound
      (fun X => dyadicPrimeFreeMeasure X theta) xi) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta ≤
        K * (((2 : ℝ) ^ m) ^ xi) := by
  rcases hbound with ⟨C, hC, hEventually⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp hEventually
  let K : ℝ := max C (max A 1)
  have hK : 0 < K :=
    zero_lt_one.trans_le ((le_max_right A 1).trans (le_max_right C (max A 1)))
  refine ⟨K, hK, ?_⟩
  intro m
  let Y : ℝ := (2 : ℝ) ^ m
  have hY : 1 ≤ Y := by
    dsimp [Y]
    exact one_le_pow₀ (by norm_num)
  have hpow : 1 ≤ Y ^ xi := Real.one_le_rpow hY hxi.le
  by_cases hlarge : A ≤ Y
  · have hAt := hA Y hlarge
    calc
      dyadicPrimeFreeMeasure Y theta ≤ |dyadicPrimeFreeMeasure Y theta| :=
        le_abs_self _
      _ ≤ C * Y ^ xi := hAt
      _ ≤ K * Y ^ xi := by
        gcongr
        exact le_max_left C (max A 1)
  · have hsmall : Y < A := lt_of_not_ge hlarge
    have hAK : A ≤ K :=
      (le_max_left A 1).trans (le_max_right C (max A 1))
    calc
      dyadicPrimeFreeMeasure Y theta ≤ Y :=
        dyadicPrimeFreeMeasure_le_scale (zero_le_one.trans hY)
      _ ≤ K := hsmall.le.trans hAK
      _ = K * 1 := by ring_nf
      _ ≤ K * Y ^ xi := mul_le_mul_of_nonneg_left hpow hK.le

theorem two_pow_rpow_eq_rpow_pow (xi : ℝ) (m : ℕ) :
    (((2 : ℝ) ^ m) ^ xi) = ((2 : ℝ) ^ xi) ^ m := by
  calc
    (((2 : ℝ) ^ m) ^ xi) = (((2 : ℝ) ^ (m : ℝ)) ^ xi) := by
      rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((m : ℝ) * xi) := by
      rw [Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (xi * (m : ℝ)) := by ring_nf
    _ = (((2 : ℝ) ^ xi) ^ (m : ℝ)) :=
      Real.rpow_mul (by norm_num) xi m
    _ = ((2 : ℝ) ^ xi) ^ m := Real.rpow_natCast _ _

/-- Tao's constant-length endpoint set is covered by the unit interval and
finitely many genuine variable-length dyadic prime-free sets. -/
theorem primeFreeEndpointSet_subset_unit_union_dyadic
    {X theta : ℝ} (htheta : 0 ≤ theta) :
    primeFreeEndpointSet X theta ⊆
      Icc 0 1 ∪ ⋃ m ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1),
        dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta := by
  intro x hx
  have hxData := mem_primeFreeEndpointSet.mp hx
  by_cases hxOne : x ≤ 1
  · exact Set.mem_union_left _ ⟨hxData.1, hxOne⟩
  · apply Set.mem_union_right
    let m := Nat.log 2 ⌊x⌋₊
    have hxAtLeastOne : 1 ≤ x := le_of_lt (lt_of_not_ge hxOne)
    have hxBlock : x ∈ Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1)) := by
      exact GafniTao.mem_dyadicBlock_natLog_floor hxAtLeastOne
    have hfloor : ⌊x⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hxData.2.1
    have hm : m < Nat.log 2 ⌊X⌋₊ + 1 := by
      exact Nat.lt_succ_of_le (Nat.log_mono_right hfloor)
    refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hm, ?_⟩⟩
    rw [mem_dyadicPrimeFreeShortSet]
    refine ⟨?_, ?_⟩
    · refine ⟨hxBlock.1, ?_⟩
      calc
        x ≤ (2 : ℝ) ^ (m + 1) := hxBlock.2.le
        _ = 2 * (2 : ℝ) ^ m := by rw [pow_succ]; ring_nf
    · intro p hp hpShort
      apply hxData.2.2 p hp
      refine ⟨hpShort.1, hpShort.2.trans ?_⟩
      have hpow : x ^ theta ≤ X ^ theta :=
        Real.rpow_le_rpow hxData.1 hxData.2.1 htheta
      linarith

/-- Measure-level finite dyadic assembly before any power estimate is
inserted.  This keeps Tao's outer length `X^theta` visible on the left. -/
theorem primeFreeEndpointMeasure_le_one_add_dyadic_sum
    {X theta : ℝ} (htheta : 0 ≤ theta) :
    primeFreeEndpointMeasure X theta ≤
      1 + ∑ m ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1),
        dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta := by
  let s : Finset ℕ := Finset.range (Nat.log 2 ⌊X⌋₊ + 1)
  let U : Set ℝ := ⋃ m ∈ s, dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta
  have hPieceFinite : ∀ m : ℕ,
      volume (dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta) < ⊤ := by
    intro m
    calc
      volume (dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta) ≤
          volume (Icc ((2 : ℝ) ^ m) (2 * (2 : ℝ) ^ m)) :=
        measure_mono (dyadicPrimeFreeShortSet_subset_Icc _ _)
      _ = ENNReal.ofReal (2 * (2 : ℝ) ^ m - (2 : ℝ) ^ m) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hUFinite : volume U ≠ ⊤ := by
    apply measure_biUnion_ne_top s.finite_toSet
    intro m _hm
    exact (hPieceFinite m).ne
  have hUnitFinite : volume (Icc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hCover : primeFreeEndpointSet X theta ⊆ Icc 0 1 ∪ U := by
    simpa only [s, U] using primeFreeEndpointSet_subset_unit_union_dyadic htheta
  change volume.real (primeFreeEndpointSet X theta) ≤
    1 + ∑ m ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1),
      volume.real (dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta)
  calc
    volume.real (primeFreeEndpointSet X theta) ≤
        volume.real (Icc 0 1 ∪ U) :=
      measureReal_mono hCover (measure_union_ne_top hUnitFinite.ne hUFinite)
    _ ≤ volume.real (Icc (0 : ℝ) 1) + volume.real U :=
      measureReal_union_le _ _
    _ = 1 + volume.real U := by simp
    _ ≤ 1 + ∑ m ∈ s,
        volume.real (dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta) := by
      gcongr
      exact measureReal_biUnion_finset_le s
        (fun m => dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta)
    _ = 1 + ∑ m ∈ Finset.range (Nat.log 2 ⌊X⌋₊ + 1),
        volume.real (dyadicPrimeFreeShortSet ((2 : ℝ) ^ m) theta) := rfl

/-- A fixed positive power bound on the genuine dyadic prime-free measures
assembles into the same fixed power bound for Tao's literal constant-length
endpoint measure. -/
theorem fixedPowerBound_primeFreeEndpointMeasure_of_dyadic
    {theta xi : ℝ} (htheta : 0 ≤ theta) (hxi : 0 < xi)
    (hdyadic : GafniTao.FixedPowerBound
      (fun X => dyadicPrimeFreeMeasure X theta) xi) :
    GafniTao.FixedPowerBound (fun X => primeFreeEndpointMeasure X theta) xi := by
  obtain ⟨K, hK, hAll⟩ :=
    uniform_dyadicPrimeFreeMeasure_bound_of_fixedPower hxi hdyadic
  let r : ℝ := (2 : ℝ) ^ xi
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hxi
  let C : ℝ := 1 + K * r / (r - 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  let L : ℕ := Nat.log 2 ⌊X⌋₊ + 1
  have hsum :
      (∑ m ∈ Finset.range L, dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta) ≤
        K * ∑ m ∈ Finset.range L, r ^ m := by
    calc
      (∑ m ∈ Finset.range L, dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta) ≤
          ∑ m ∈ Finset.range L, K * (((2 : ℝ) ^ m) ^ xi) := by
        exact Finset.sum_le_sum fun m _hm => hAll m
      _ = ∑ m ∈ Finset.range L, K * r ^ m := by
        apply Finset.sum_congr rfl
        intro m _hm
        rw [two_pow_rpow_eq_rpow_pow]
      _ = K * ∑ m ∈ Finset.range L, r ^ m := by
        rw [Finset.mul_sum]
  have hgeom :
      (∑ m ∈ Finset.range L, r ^ m) ≤ r ^ L / (r - 1) := by
    rw [geom_sum_eq hr.ne']
    exact div_le_div_of_nonneg_right
      (by linarith [pow_nonneg (zero_le_one.trans hr.le) L])
      (sub_nonneg.mpr hr.le)
  have hfloorNe : ⌊X⌋₊ ≠ 0 := by
    have hfloorOne : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
    omega
  have hbaseNat : 2 ^ Nat.log 2 ⌊X⌋₊ ≤ ⌊X⌋₊ :=
    Nat.pow_log_le_self 2 hfloorNe
  have hbase : (2 : ℝ) ^ Nat.log 2 ⌊X⌋₊ ≤ X := by
    have hcast : ((2 ^ Nat.log 2 ⌊X⌋₊ : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
      exact_mod_cast hbaseNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      hcast.trans (Nat.floor_le (zero_le_one.trans hX))
  have hscale : (2 : ℝ) ^ L ≤ 2 * X := by
    dsimp [L]
    rw [pow_succ]
    linarith
  have hrL : r ^ L ≤ r * X ^ xi := by
    calc
      r ^ L = (((2 : ℝ) ^ L) ^ xi) :=
        (two_pow_rpow_eq_rpow_pow xi L).symm
      _ ≤ (2 * X) ^ xi := by
        exact Real.rpow_le_rpow (by positivity) hscale hxi.le
      _ = r * X ^ xi := by
        dsimp [r]
        rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hX)]
  have hpowOne : 1 ≤ X ^ xi := Real.one_le_rpow hX hxi.le
  have hmeasure := primeFreeEndpointMeasure_le_one_add_dyadic_sum
    (X := X) htheta
  have hsumFinal :
      (∑ m ∈ Finset.range L, dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta) ≤
        (K * r / (r - 1)) * X ^ xi := by
    calc
      _ ≤ K * ∑ m ∈ Finset.range L, r ^ m := hsum
      _ ≤ K * (r ^ L / (r - 1)) := by gcongr
      _ ≤ K * ((r * X ^ xi) / (r - 1)) := by gcongr
      _ = (K * r / (r - 1)) * X ^ xi := by ring_nf
  rw [abs_of_nonneg (show 0 ≤ primeFreeEndpointMeasure X theta from
    ENNReal.toReal_nonneg)]
  calc
    primeFreeEndpointMeasure X theta ≤
        1 + ∑ m ∈ Finset.range L,
          dyadicPrimeFreeMeasure ((2 : ℝ) ^ m) theta := by
      simpa only [L] using hmeasure
    _ ≤ 1 + (K * r / (r - 1)) * X ^ xi := by linarith
    _ ≤ C * X ^ xi := by
      dsimp [C]
      have hcoef : 0 ≤ K * r / (r - 1) := by positivity
      nlinarith

/-- A fixed-power bound is stronger than the corresponding `a+o(1)` power
bound used in Tao's statement. -/
theorem epsilonExponentBound_of_fixedPowerBound
    {f : ℝ → ℝ} {a : ℝ} (h : GafniTao.FixedPowerBound f a) :
    GafniTao.EpsilonExponentBound f a := by
  rcases h with ⟨C, hC, hEventually⟩
  intro epsilon hepsilon
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hEventually, eventually_ge_atTop (1 : ℝ)] with X hX hXOne
  have hXNonneg : 0 ≤ X := zero_le_one.trans hXOne
  have hpowerEpsilon : 1 ≤ X ^ epsilon :=
    Real.one_le_rpow hXOne hepsilon.le
  have hpowerA : 0 ≤ X ^ a := Real.rpow_nonneg hXNonneg a
  calc
    ‖|f X|‖ = |f X| := by simp
    _ ≤ C * X ^ a := hX
    _ ≤ C * (X ^ epsilon * |X ^ a|) := by
      rw [abs_of_nonneg hpowerA]
      apply mul_le_mul_of_nonneg_left _ hC.le
      calc
        X ^ a = 1 * X ^ a := by ring_nf
        _ ≤ X ^ epsilon * X ^ a :=
          mul_le_mul_of_nonneg_right hpowerEpsilon hpowerA
    _ = C * ‖X ^ epsilon * |X ^ a|‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg hXNonneg epsilon) (abs_nonneg _))]

theorem primeFreeEndpointSet_subset_Icc (X theta : ℝ) :
    primeFreeEndpointSet X theta ⊆ Icc 0 X := by
  intro x hx
  exact ⟨(mem_primeFreeEndpointSet.mp hx).1,
    (mem_primeFreeEndpointSet.mp hx).2.1⟩

theorem measure_primeFreeEndpointSet_lt_top (X theta : ℝ) :
    volume (primeFreeEndpointSet X theta) < ⊤ := by
  calc
    volume (primeFreeEndpointSet X theta) ≤ volume (Icc 0 X) :=
      measure_mono (primeFreeEndpointSet_subset_Icc X theta)
    _ = ENNReal.ofReal (X - 0) := Real.volume_Icc
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- At outer scales at least one, increasing the short-interval exponent can
only shrink Tao's prime-free endpoint set. -/
theorem primeFreeEndpointSet_anti_theta
    {X theta₀ theta : ℝ} (hX : 1 ≤ X) (htheta : theta₀ ≤ theta) :
    primeFreeEndpointSet X theta ⊆ primeFreeEndpointSet X theta₀ := by
  intro x hx
  have hxData := mem_primeFreeEndpointSet.mp hx
  rw [mem_primeFreeEndpointSet]
  refine ⟨hxData.1, hxData.2.1, ?_⟩
  intro p hp hpShort
  apply hxData.2.2 p hp
  refine ⟨hpShort.1, hpShort.2.trans ?_⟩
  gcongr

theorem primeFreeEndpointMeasure_anti_theta
    {X theta₀ theta : ℝ} (hX : 1 ≤ X) (htheta : theta₀ ≤ theta) :
    primeFreeEndpointMeasure X theta ≤ primeFreeEndpointMeasure X theta₀ := by
  change volume.real (primeFreeEndpointSet X theta) ≤
    volume.real (primeFreeEndpointSet X theta₀)
  exact measureReal_mono (primeFreeEndpointSet_anti_theta hX htheta)
    (measure_primeFreeEndpointSet_lt_top X theta₀).ne

theorem fixedPowerBound_primeFreeEndpointMeasure_anti_theta
    {theta₀ theta xi : ℝ} (htheta : theta₀ ≤ theta)
    (hbound : GafniTao.FixedPowerBound
      (fun X => primeFreeEndpointMeasure X theta₀) xi) :
    GafniTao.FixedPowerBound
      (fun X => primeFreeEndpointMeasure X theta) xi := by
  apply hbound.mono_eventually
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  rw [abs_of_nonneg (show 0 ≤ primeFreeEndpointMeasure X theta from
      ENNReal.toReal_nonneg),
    abs_of_nonneg (show 0 ≤ primeFreeEndpointMeasure X theta₀ from
      ENNReal.toReal_nonneg)]
  exact primeFreeEndpointMeasure_anti_theta hX htheta

/-- After the explicit prime-power threshold, the entire dyadic prime-free set
is contained in the Gafni--Tao discrepancy exceptional set. -/
theorem eventually_dyadicPrimeFreeShortSet_subset_exceptional
    {theta : ℝ} (htheta : 0 < theta) (hthetaUpper : theta ≤ 1) :
    ∀ᶠ X : ℝ in atTop,
      dyadicPrimeFreeShortSet X theta ⊆
        GafniTao.shortIntervalExceptionalSet (1 / 2) X theta := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_primePowerTailIntervalSum_le_half htheta hthetaUpper)
  filter_upwards [eventually_ge_atTop (max M 0)] with X hX
  intro x hx
  have hxData := mem_dyadicPrimeFreeShortSet.mp hx
  have hxNonneg : 0 ≤ x := (le_max_right M 0).trans hX |>.trans hxData.1.1
  apply mem_shortIntervalExceptionalSet_half_of_primeFree hxData.1 hxNonneg hxData.2
  exact hM x ((le_max_left M 0).trans hX |>.trans hxData.1.1)

/-- Eventual set containment transfers Gafni--Tao's fixed-power estimate to
the genuine dyadic prime-free endpoint measure. -/
theorem fixedPowerBound_dyadicPrimeFreeMeasure
    {theta xi : ℝ} (htheta : 0 < theta) (hthetaUpper : theta ≤ 1)
    (hbound : GafniTao.FixedPowerBound
      (fun X => GafniTao.exceptionalMeasure (1 / 2) X theta) xi) :
    GafniTao.FixedPowerBound (fun X => dyadicPrimeFreeMeasure X theta) xi := by
  apply hbound.mono_eventually
  filter_upwards [eventually_dyadicPrimeFreeShortSet_subset_exceptional
    htheta hthetaUpper] with X hsubset
  change |(volume (dyadicPrimeFreeShortSet X theta)).toReal| ≤
    |(volume (GafniTao.shortIntervalExceptionalSet (1 / 2) X theta)).toReal|
  rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono
    (GafniTao.measure_shortIntervalExceptionalSet_lt_top
      (1 / 2) X theta).ne
    (measure_mono hsubset)

/-- The frozen Guth--Maynard/Gafni--Tao chain supplies a uniform fixed power
below one for the literal dyadic short-interval exceptional measures. -/
theorem exists_uniform_dyadic_exceptional_power_guthMaynard
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    ∃ xi : ℝ, xi < 1 ∧
      ∀ delta : ℝ, 0 < delta →
        GafniTao.FixedPowerBound
          (fun X => GafniTao.exceptionalMeasure delta X theta) xi := by
  obtain ⟨c, Tzero, Tdensity, hc, _hZeroFree, hDensity⟩ :=
    GafniTao.exists_pintz_nearOne_log_density_native
  have hmu : GafniTao.exceptionalExponent theta < (1 : EReal) :=
    GafniTao.exceptionalExponent_lt_one_of_uniform_density hDensity
      GafniTao.pintzNearOneDensityCoefficient_pos
      (by norm_num : (0 : ℝ) < 30 / 13) (by linarith) hthetaUpper
      GafniTao.uniformOrdinaryDensityExponent_thirty_thirteenths (by
        rw [← GafniTao.two_fifteenths_eq_uniform_almost_all_threshold]
        exact htheta)
  obtain ⟨xi, hmuXi, hxiOne⟩ := EReal.exists_between_coe_real hmu
  refine ⟨xi, by exact_mod_cast hxiOne, ?_⟩
  intro delta hdelta
  apply GafniTao.fixedPowerBound_of_leastFixedPowerExponent_lt
  exact (GafniTao.exceptionalExponentDelta_le_exceptionalExponent hdelta).trans_lt
    hmuXi

/-- Quantitative dyadic prime-free consequence in the form directly consumed
by the remaining dyadic-to-prefix argument.  The exponent is normalized to be
nonnegative without losing the strict saving below one. -/
theorem exists_dyadic_primeFree_power_guthMaynard
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    ∃ xi : ℝ, 0 < xi ∧ xi < 1 ∧
      GafniTao.FixedPowerBound (fun X => dyadicPrimeFreeMeasure X theta) xi := by
  obtain ⟨xi, hxi, hbound⟩ :=
    exists_uniform_dyadic_exceptional_power_guthMaynard htheta hthetaUpper
  let eta : ℝ := max xi (1 / 2)
  have hetaPos : 0 < eta := (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_le
    (le_max_right xi (1 / 2))
  have hetaOne : eta < 1 := max_lt hxi (by norm_num)
  have hthetaPos : 0 < theta := (by norm_num : (0 : ℝ) < 2 / 15) |>.trans htheta
  have hhalf : GafniTao.FixedPowerBound
      (fun X => GafniTao.exceptionalMeasure (1 / 2) X theta) xi :=
    hbound (1 / 2) (by norm_num)
  have hprimeFree : GafniTao.FixedPowerBound
      (fun X => dyadicPrimeFreeMeasure X theta) xi :=
    fixedPowerBound_dyadicPrimeFreeMeasure hthetaPos hthetaUpper.le hhalf
  exact ⟨eta, hetaPos, hetaOne,
    hprimeFree.mono_exponent (le_max_left xi (1 / 2))⟩

/-- Tao Proposition 2.3(iii) in the nontrivial source range below one.  The
remaining `theta ≥ 1` range follows by monotonicity of the interval length and
is kept separate so that this theorem records exactly where Guth--Maynard is
used. -/
theorem taoProposition23iii_of_lt_one
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    ∃ c : ℝ, 0 < c ∧
      GafniTao.EpsilonExponentBound
        (fun X => primeFreeEndpointMeasure X theta) (1 - c) := by
  obtain ⟨xi, hxiPos, hxiOne, hdyadic⟩ :=
    exists_dyadic_primeFree_power_guthMaynard htheta hthetaUpper
  have hglobal : GafniTao.FixedPowerBound
      (fun X => primeFreeEndpointMeasure X theta) xi :=
    fixedPowerBound_primeFreeEndpointMeasure_of_dyadic (by linarith)
      hxiPos hdyadic
  refine ⟨1 - xi, sub_pos.mpr hxiOne, ?_⟩
  simpa only [sub_sub_cancel] using
    epsilonExponentBound_of_fixedPowerBound hglobal

/-- Tao's Proposition 2.3(iii), with the paper's full range `theta > 2/15`,
literal closed intervals, real endpoints in `[0,X]`, and the quantified
`O(X^(1-c+o(1)))` convention. -/
theorem taoProposition23iii_guthMaynard
    {theta : ℝ} (htheta : 2 / 15 < theta) :
    ∃ c : ℝ, 0 < c ∧
      GafniTao.EpsilonExponentBound
        (fun X => primeFreeEndpointMeasure X theta) (1 - c) := by
  by_cases hthetaUpper : theta < 1
  · exact taoProposition23iii_of_lt_one htheta hthetaUpper
  · have hhalfLower : (2 / 15 : ℝ) < 1 / 2 := by norm_num
    have hhalfUpper : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨xi, hxiPos, hxiOne, hdyadic⟩ :=
      exists_dyadic_primeFree_power_guthMaynard hhalfLower hhalfUpper
    have hhalfGlobal : GafniTao.FixedPowerBound
        (fun X => primeFreeEndpointMeasure X (1 / 2)) xi :=
      fixedPowerBound_primeFreeEndpointMeasure_of_dyadic (by norm_num)
        hxiPos hdyadic
    have hthetaGlobal : GafniTao.FixedPowerBound
        (fun X => primeFreeEndpointMeasure X theta) xi :=
      fixedPowerBound_primeFreeEndpointMeasure_anti_theta
        (by linarith : (1 / 2 : ℝ) ≤ theta) hhalfGlobal
    refine ⟨1 - xi, sub_pos.mpr hxiOne, ?_⟩
    simpa only [sub_sub_cancel] using
      epsilonExponentBound_of_fixedPowerBound hthetaGlobal

end

end Tao2026
