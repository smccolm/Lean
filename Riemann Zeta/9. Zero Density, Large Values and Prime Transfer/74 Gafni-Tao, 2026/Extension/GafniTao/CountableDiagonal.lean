import GafniTao.ExceptionalDensity
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The countable exceptional-set diagonal

This file implements the diagonalization requested immediately after
Definition 1.1 of Gafni--Tao.  The construction is deliberately performed on
the literal dyadic exceptional sets: the discrepancy threshold is allowed to
decrease slowly with the dyadic block, while the relative measure of the
selected block still tends to zero.
-/

open Asymptotics Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

/-- A countable family of eventual predicates admits a slowly increasing
diagonal.  Only an eventual diagonal conclusion is asserted, since finitely
many initial indices play no role in the source asymptotics. -/
theorem exists_tendsto_nat_diagonal
    (P : ℕ → ℕ → Prop) (hP : ∀ n, ∀ᶠ m in atTop, P n m) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ᶠ m in atTop, P (q m) m := by
  classical
  choose base hbase using fun n => (eventually_atTop.1 (hP n))
  let cutoff : ℕ → ℕ := fun n =>
    Nat.rec (base 0)
      (fun k previous => max (base (k + 1)) (previous + 1)) n
  have hcutoff_succ (n : ℕ) :
      cutoff (n + 1) = max (base (n + 1)) (cutoff n + 1) := by
    rfl
  have hbase_le_cutoff : ∀ n, base n ≤ cutoff n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [hcutoff_succ]
        exact le_max_left _ _
  have hindex_le_cutoff : ∀ n, n ≤ cutoff n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        rw [hcutoff_succ]
        exact (Nat.succ_le_succ ih).trans (le_max_right _ _)
  have hcutoff_condition {n m : ℕ} (hnm : cutoff n ≤ m) : P n m :=
    hbase n m ((hbase_le_cutoff n).trans hnm)
  let q : ℕ → ℕ := fun m =>
    @Nat.findGreatest (fun n => cutoff n ≤ m) (Classical.decPred _) m
  have hq_tendsto : Tendsto q atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro n
    refine ⟨cutoff n, fun m hm => ?_⟩
    dsimp only [q]
    exact @Nat.le_findGreatest n (fun k => cutoff k ≤ m) (Classical.decPred _)
      m ((hindex_le_cutoff n).trans hm) hm
  refine ⟨q, hq_tendsto, ?_⟩
  filter_upwards [eventually_ge_atTop (cutoff 0)] with m hm
  have hspec : cutoff (q m) ≤ m := by
    dsimp only [q]
    exact @Nat.findGreatest_spec 0 (fun n => cutoff n ≤ m) (Classical.decPred _)
      m (Nat.zero_le m) hm
  exact hcutoff_condition hspec

/-- Dyadic specialization of the fixed-threshold density-zero statements.
The selected discrepancy threshold tends to zero and the selected literal
exceptional-set measure is `o(2^m)`. -/
theorem exists_dyadic_exceptional_diagonal
    {theta : ℝ} (hDensity : DyadicExceptionalDensityZero theta) :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto
        (fun m : ℕ =>
          exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta /
            (2 : ℝ) ^ m)
        atTop (𝓝 0) := by
  let P : ℕ → ℕ → Prop := fun n m =>
    exceptionalMeasure (1 / (n + 1 : ℝ)) ((2 : ℝ) ^ m) theta /
        (2 : ℝ) ^ m ≤ 1 / (n + 1 : ℝ)
  have hP : ∀ n, ∀ᶠ m in atTop, P n m := by
    intro n
    have hdelta : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hcomp := (hDensity (1 / (n + 1 : ℝ)) hdelta).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    exact (hcomp.eventually (eventually_le_nhds (by positivity))).mono fun m hm => hm
  obtain ⟨q, hq, hDiagonal⟩ := exists_tendsto_nat_diagonal P hP
  refine ⟨q, hq, ?_⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun m =>
      div_nonneg ENNReal.toReal_nonneg (by positivity)
  · filter_upwards [hDiagonal] with m hm
    exact hm
  · exact tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.comp hq).atTop_add tendsto_const_nhds)

/-- Every real `x ≥ 1` lies in the closed dyadic block indexed by the binary
logarithm of its natural floor. -/
theorem mem_dyadicBlock_natLog_floor {x : ℝ} (hx : 1 ≤ x) :
    x ∈ Ico
      ((2 : ℝ) ^ Nat.log 2 ⌊x⌋₊)
      ((2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloor_ne : ⌊x⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt this)
  have hlowerNat : 2 ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ :=
    Nat.pow_log_le_self 2 hfloor_ne
  have hupperNat : ⌊x⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) ⌊x⌋₊
  constructor
  · have hlowerCast : ((2 ^ Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast hlowerNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      hlowerCast.trans (Nat.floor_le hx0)
  · have hxFloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hcast : (⌊x⌋₊ : ℝ) + 1 ≤
        (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) := by exact_mod_cast hupperNat
    exact hxFloor.trans_le hcast

/-- The binary logarithm of the natural floor tends to infinity with its
real argument. -/
theorem tendsto_natLog_two_floor_atTop :
    Tendsto (fun x : ℝ => Nat.log 2 ⌊x⌋₊) atTop atTop := by
  have hlog : Tendsto (Nat.log 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro n
    refine ⟨2 ^ n, fun k hk => ?_⟩
    exact Nat.le_log_of_pow_le (by norm_num) hk
  exact hlog.comp tendsto_nat_floor_atTop

/-- The half-open dyadic piece of the selected literal exceptional set. -/
noncomputable def dyadicExceptionalPiece
    (theta : ℝ) (q : ℕ → ℕ) (m : ℕ) : Set ℝ :=
  shortIntervalExceptionalSet
      (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta ∩
    Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1))

/-- The single exceptional set produced by the paper's countable
diagonalization. -/
noncomputable def diagonalExceptionalSet
    (theta : ℝ) (q : ℕ → ℕ) : Set ℝ :=
  ⋃ m : ℕ, dyadicExceptionalPiece theta q m

theorem measurableSet_dyadicExceptionalPiece
    {theta : ℝ} (htheta : 0 ≤ theta) (q : ℕ → ℕ) (m : ℕ) :
    MeasurableSet (dyadicExceptionalPiece theta q m) := by
  exact (measurableSet_shortIntervalExceptionalSet _ _ htheta).inter
    measurableSet_Ico

theorem measurableSet_diagonalExceptionalSet
    {theta : ℝ} (htheta : 0 ≤ theta) (q : ℕ → ℕ) :
    MeasurableSet (diagonalExceptionalSet theta q) := by
  exact MeasurableSet.iUnion fun m =>
    measurableSet_dyadicExceptionalPiece htheta q m

/-- Source-facing meaning of the prime number theorem outside one exceptional
set.  The quantifier is over every fixed relative-error threshold. -/
def ShortIntervalPNTOutside (theta : ℝ) (E : Set ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∀ᶠ x : ℝ in atTop, x ∉ E →
      |shortIntervalDiscrepancy x theta| < delta * x ^ theta

/-- Outside the single diagonal set, all reciprocal-integer discrepancy
thresholds are eventually avoided, hence the full short-interval asymptotic
holds. -/
theorem shortIntervalPNTOutside_diagonalExceptionalSet
    {theta : ℝ} {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ShortIntervalPNTOutside theta (diagonalExceptionalSet theta q) := by
  intro delta hdelta
  have hindex : Tendsto (fun x : ℝ => q (Nat.log 2 ⌊x⌋₊)) atTop atTop :=
    hq.comp tendsto_natLog_two_floor_atTop
  have hthreshold : ∀ᶠ x : ℝ in atTop,
      1 / (q (Nat.log 2 ⌊x⌋₊) + 1 : ℝ) < delta := by
    have hlim : Tendsto
        (fun x : ℝ => 1 / (q (Nat.log 2 ⌊x⌋₊) + 1 : ℝ))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop.comp hindex).atTop_add tendsto_const_nhds)
    exact hlim.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hthreshold, eventually_ge_atTop (1 : ℝ)] with x hsmall hx
  intro hxOutside
  let m := Nat.log 2 ⌊x⌋₊
  have hxBlock : x ∈ Ico ((2 : ℝ) ^ m) ((2 : ℝ) ^ (m + 1)) := by
    simpa only [m] using mem_dyadicBlock_natLog_floor hx
  have hxNonneg : 0 ≤ x := zero_le_one.trans hx
  have hpow : 0 ≤ x ^ theta := Real.rpow_nonneg hxNonneg theta
  have hNotLarge :
      ¬(1 / (q m + 1 : ℝ)) * x ^ theta ≤
        |shortIntervalDiscrepancy x theta| := by
    intro hLarge
    have hxSource : x ∈ shortIntervalExceptionalSet
        (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta := by
      refine ⟨?_, hLarge⟩
      constructor
      · exact hxBlock.1
      · rw [show 2 * ((2 : ℝ) ^ m) = (2 : ℝ) ^ (m + 1) by
          rw [pow_succ]; ring]
        exact hxBlock.2.le
    have hxPiece : x ∈ dyadicExceptionalPiece theta q m := ⟨hxSource, hxBlock⟩
    exact hxOutside (Set.mem_iUnion.2 ⟨m, hxPiece⟩)
  have hExact : |shortIntervalDiscrepancy x theta| <
      (1 / (q m + 1 : ℝ)) * x ^ theta := lt_of_not_ge hNotLarge
  exact hExact.trans_le (mul_le_mul_of_nonneg_right hsmall.le hpow)

/-- A geometrically weighted Cesaro lemma tailored to dyadic exceptional
blocks.  This is the quantitative summation step that turns blockwise
`o(2^m)` into prefix `o(2^M)`. -/
theorem tendsto_weighted_dyadic_average_zero
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto
      (fun M : ℕ =>
        (∑ m ∈ Finset.range M, r m * (2 : ℝ) ^ m) / (2 : ℝ) ^ M)
      atTop (𝓝 0) := by
  have hrLittle : r =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hr
  have hterm :
      (fun m : ℕ => r m * (2 : ℝ) ^ m) =o[atTop]
        (fun m : ℕ => (2 : ℝ) ^ m) := by
    simpa only [one_mul] using
      hrLittle.mul_isBigO
        (isBigO_refl (fun m : ℕ => (2 : ℝ) ^ m) atTop)
  have hGeomTop : Tendsto
      (fun M : ℕ => ∑ m ∈ Finset.range M, (2 : ℝ) ^ m) atTop atTop := by
    refine tendsto_atTop_mono' atTop
      (f₁ := fun M : ℕ => (2 : ℝ) ^ M - 1)
      (f₂ := fun M : ℕ => ∑ m ∈ Finset.range M, (2 : ℝ) ^ m)
      (Eventually.of_forall fun M => by
      dsimp only
      rw [← geom_sum_mul (2 : ℝ) M]
      norm_num) ?_
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hsum := hterm.sum_range (fun m => by positivity) hGeomTop
  have hGeomBigO :
      (fun M : ℕ => ∑ m ∈ Finset.range M, (2 : ℝ) ^ m) =O[atTop]
        (fun M : ℕ => (2 : ℝ) ^ M) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun M => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
      have hGeom := geom_sum_mul_add (1 : ℝ) M
      norm_num at hGeom ⊢
      linarith
  exact (hsum.trans_isBigO hGeomBigO).tendsto_div_nhds_zero

theorem measureReal_dyadicExceptionalPiece_le
    (theta : ℝ) (q : ℕ → ℕ) (m : ℕ) :
    volume.real (dyadicExceptionalPiece theta q m) ≤
      exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta := by
  exact measureReal_mono inter_subset_left
    (h₂ := (measure_shortIntervalExceptionalSet_lt_top
      (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta).ne)

/-- Up to the right endpoint `2^M`, the diagonal set only uses its first
`M` half-open dyadic pieces. -/
theorem diagonalExceptionalSet_inter_dyadicPrefix_subset
    (theta : ℝ) (q : ℕ → ℕ) (M : ℕ) :
    diagonalExceptionalSet theta q ∩ Ico 1 ((2 : ℝ) ^ M) ⊆
      ⋃ m ∈ Finset.range M, dyadicExceptionalPiece theta q m := by
  intro x hx
  obtain ⟨m, hxm⟩ := Set.mem_iUnion.1 hx.1
  have hmPow : (2 : ℝ) ^ m < (2 : ℝ) ^ M := hxm.2.1.trans_lt hx.2.2
  have hm : m < M := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hmPow
  exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hm, hxm⟩⟩

/-- Finite-prefix measure estimate for the exact diagonal set. -/
theorem measureReal_diagonalExceptionalSet_dyadicPrefix_le
    (theta : ℝ) (q : ℕ → ℕ) (M : ℕ) :
    volume.real
        (diagonalExceptionalSet theta q ∩ Ico 1 ((2 : ℝ) ^ M)) ≤
      ∑ m ∈ Finset.range M,
        exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta := by
  let U : Set ℝ := ⋃ m ∈ Finset.range M, dyadicExceptionalPiece theta q m
  have hUFinite : volume U ≠ ⊤ := by
    apply measure_biUnion_ne_top (Finset.range M).finite_toSet
    intro m hm
    exact ((measure_mono inter_subset_left).trans_lt
      (measure_shortIntervalExceptionalSet_lt_top
        (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta)).ne
  calc
    volume.real
        (diagonalExceptionalSet theta q ∩ Ico 1 ((2 : ℝ) ^ M)) ≤
        volume.real U :=
      measureReal_mono
        (diagonalExceptionalSet_inter_dyadicPrefix_subset theta q M) hUFinite
    _ ≤ ∑ m ∈ Finset.range M,
        volume.real (dyadicExceptionalPiece theta q m) :=
      measureReal_biUnion_finset_le (Finset.range M)
        (dyadicExceptionalPiece theta q)
    _ ≤ ∑ m ∈ Finset.range M,
        exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta := by
      exact Finset.sum_le_sum fun m _ =>
        measureReal_dyadicExceptionalPiece_le theta q m

/-- Prefix density zero in the ordinary real-variable sense. -/
def NaturalDensityZero (E : Set ℝ) : Prop :=
  Tendsto (fun X : ℝ => volume.real (E ∩ Ico 1 X) / X) atTop (𝓝 0)

/-- The blockwise diagonal estimate gives `o(2^M)` measure on dyadic
prefixes. -/
theorem diagonalExceptionalSet_dyadicPrefix_densityZero
    {theta : ℝ} {q : ℕ → ℕ}
    (hMeasure : Tendsto
      (fun m : ℕ =>
        exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta /
          (2 : ℝ) ^ m)
      atTop (𝓝 0)) :
    Tendsto
      (fun M : ℕ =>
        volume.real
            (diagonalExceptionalSet theta q ∩ Ico 1 ((2 : ℝ) ^ M)) /
          (2 : ℝ) ^ M)
      atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun m =>
    exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta /
      (2 : ℝ) ^ m
  have hAverage := tendsto_weighted_dyadic_average_zero (r := r) hMeasure
  have hAverage' : Tendsto
      (fun M : ℕ =>
        (∑ m ∈ Finset.range M,
          exceptionalMeasure (1 / (q m + 1 : ℝ)) ((2 : ℝ) ^ m) theta) /
            (2 : ℝ) ^ M)
      atTop (𝓝 0) := by
    simpa only [r,
      div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] using hAverage
  apply squeeze_zero'
  · exact Eventually.of_forall fun M =>
      div_nonneg MeasureTheory.measureReal_nonneg (by positivity)
  · exact Eventually.of_forall fun M => by
      exact div_le_div_of_nonneg_right
        (measureReal_diagonalExceptionalSet_dyadicPrefix_le theta q M)
        (by positivity)
  · exact hAverage'

/-- A dyadic prefix density-zero estimate is an ordinary prefix
density-zero estimate.  The factor two comes only from enclosing an arbitrary
right endpoint in its next dyadic boundary. -/
theorem naturalDensityZero_of_dyadicPrefix
    {E : Set ℝ}
    (hDyadic : Tendsto
      (fun M : ℕ => volume.real (E ∩ Ico 1 ((2 : ℝ) ^ M)) /
        (2 : ℝ) ^ M)
      atTop (𝓝 0)) :
    NaturalDensityZero E := by
  let index : ℝ → ℕ := fun X => Nat.log 2 ⌊X⌋₊ + 1
  have hindex : Tendsto index atTop atTop := by
    simpa only [index, Function.comp_apply] using
      (tendsto_add_atTop_nat 1).comp tendsto_natLog_two_floor_atTop
  have hMajorant : Tendsto
      (fun X : ℝ =>
        2 * (volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) /
          (2 : ℝ) ^ index X)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (hDyadic.comp hindex).const_mul 2
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg MeasureTheory.measureReal_nonneg (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hxBlock := mem_dyadicBlock_natLog_floor hX
    have hXPos : 0 < X := zero_lt_one.trans_le hX
    have hIndexPow : (2 : ℝ) ^ index X ≤ 2 * X := by
      dsimp only [index]
      rw [pow_succ]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hxBlock.1 (by norm_num : (0 : ℝ) ≤ 2)
    have hXUpper : X ≤ (2 : ℝ) ^ index X := by
      dsimp only [index]
      exact hxBlock.2.le
    have hSubset : E ∩ Ico 1 X ⊆ E ∩ Ico 1 ((2 : ℝ) ^ index X) := by
      intro x hx
      exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hXUpper⟩
    have hMeasureMono : volume.real (E ∩ Ico 1 X) ≤
        volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) := by
      exact measureReal_mono hSubset
        (h₂ := ((measure_mono inter_subset_right).trans_lt measure_Ico_lt_top).ne)
    have hPowPos : 0 < (2 : ℝ) ^ index X := by positivity
    calc
      volume.real (E ∩ Ico 1 X) / X ≤
          volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) / X :=
        div_le_div_of_nonneg_right hMeasureMono hXPos.le
      _ ≤ 2 * (volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) /
          (2 : ℝ) ^ index X) := by
        have hMeasureNonneg : 0 ≤
            volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) :=
          MeasureTheory.measureReal_nonneg
        calc
          volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) / X ≤
              volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) /
                ((2 : ℝ) ^ index X / 2) :=
            div_le_div_of_nonneg_left hMeasureNonneg (by positivity) (by linarith)
          _ = 2 * (volume.real (E ∩ Ico 1 ((2 : ℝ) ^ index X)) /
              (2 : ℝ) ^ index X) := by
            field_simp [hPowPos.ne']
  · exact hMajorant

/-- The same selected set simultaneously supports the asymptotic and has
ordinary density zero. -/
theorem exists_densityZero_exceptionalSet_of_dyadic
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hDensity : DyadicExceptionalDensityZero theta) :
    ∃ E : Set ℝ,
      MeasurableSet E ∧ NaturalDensityZero E ∧
        ShortIntervalPNTOutside theta E := by
  obtain ⟨q, hq, hMeasure⟩ := exists_dyadic_exceptional_diagonal hDensity
  refine ⟨diagonalExceptionalSet theta q,
    measurableSet_diagonalExceptionalSet htheta q, ?_,
    shortIntervalPNTOutside_diagonalExceptionalSet hq⟩
  exact naturalDensityZero_of_dyadicPrefix
    (diagonalExceptionalSet_dyadicPrefix_densityZero hMeasure)

/-- Final countable-diagonal consequence of `mu(theta) < 1`. -/
theorem exists_densityZero_exceptionalSet_of_exceptionalExponent_lt_one
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hmu : exceptionalExponent theta < (1 : EReal)) :
    ∃ E : Set ℝ,
      MeasurableSet E ∧ NaturalDensityZero E ∧
        ShortIntervalPNTOutside theta E :=
  exists_densityZero_exceptionalSet_of_dyadic htheta
    (exceptionalExponent_lt_one_dyadicDensityZero hmu)

end

end GafniTao
