import Tao2026.BadIntervalDyadicSummation
import Tao2026.SmoothNumberSaddleCurvature

/-!
# Regular variation of the one-term bad-set count

The exact identity for `badOneTermCount` is a sum of smooth-number counts
indexed by the distinguished prime.  This file constructs a slowly widening
prime band around the saddle scale `taoZ`, proves that every selector from the
band is in the exponent-one critical smooth-number regime, and upgrades the
sequence-form dilation limit to a uniform dilation limit for the whole finite
central sum.

The remaining step is to show that the complementary prime ranges have
negligible mass.  That step is elementary once the fixed-row estimates in
`BadIntervalSlowCutoff` are assembled; it is kept explicit below rather than
hidden in the adjacent-dyadic hypothesis.
-/

namespace Tao2026

open Filter Finset Asymptotics
open scoped Topology Real BigOperators

noncomputable section

/-- The exact prime portion of the one-term sum between the slowly moving
cutoffs `z^(1-2/d)` and `z^(1+2/d)`. -/
noncomputable def taoSlowCentralOneTermPrimeRange (n x : ℕ) : Finset ℕ :=
  taoOneTermExponentPrimeBand (taoSlowLowerExponent n)
    (taoSlowUpperExponent n) x

/-- The central contribution to the exact one-term identity. -/
noncomputable def taoSlowCentralOneTermMass (n x : ℕ) : ℝ :=
  ∑ p ∈ taoSlowCentralOneTermPrimeRange n x,
    (psiNat (x / p ^ 2) p : ℝ)

/-- The same central prime packet with the smooth cofactor cutoff doubled
after natural division. -/
noncomputable def taoSlowCentralOneTermDoubledMass (n x : ℕ) : ℝ :=
  ∑ p ∈ taoSlowCentralOneTermPrimeRange n x,
    (psiNat (2 * (x / p ^ 2)) p : ℝ)

/-- The central packet evaluated at the halved ambient cutoff. -/
noncomputable def taoSlowCentralOneTermHalvedMass (n x : ℕ) : ℝ :=
  ∑ p ∈ taoSlowCentralOneTermPrimeRange n x,
    (psiNat ((x / 2) / p ^ 2) p : ℝ)

/-- The complementary contribution in the exact prime sum. -/
noncomputable def taoSlowOutsideOneTermMass (n x : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 2 x.sqrt).filter Nat.Prime) \
      taoSlowCentralOneTermPrimeRange n x,
    (psiNat (x / p ^ 2) p : ℝ)

theorem taoSlowLowerExponent_lt_upper (n : ℕ) :
    taoSlowLowerExponent n < taoSlowUpperExponent n := by
  have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  rw [taoSlowLowerExponent, taoSlowUpperExponent]
  have htwo : (0 : ℝ) < 2 / taoSlowCutoffDenominator n := by
    positivity
  linarith

/-- Every fixed row contains primes for all sufficiently large ambient
cutoffs. -/
theorem eventually_taoSlowCentralOneTermPrimeRange_nonempty (n : ℕ) :
    ∀ᶠ x : ℕ in atTop, (taoSlowCentralOneTermPrimeRange n x).Nonempty := by
  simpa only [taoSlowCentralOneTermPrimeRange] using
    eventually_exponentPrimeBand_nonempty (taoSlowLowerExponent_pos n)
      (taoSlowLowerExponent_lt_upper n)

/-- A slowly increasing row can be selected while retaining nonemptiness of
the moving central prime band. -/
theorem exists_taoSlowCentralOneTermDiagonal :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      (∀ᶠ x : ℕ in atTop,
        (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) := by
  let P : ℕ → ℕ → Prop := fun n x =>
    (taoSlowCentralOneTermPrimeRange n x).Nonempty
  have hP : ∀ n, ∀ᶠ x : ℕ in atTop, P n x := by
    intro n
    simpa only [P] using eventually_taoSlowCentralOneTermPrimeRange_nonempty n
  obtain ⟨q, hq, hselected⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  exact ⟨q, hq, by simpa only [P] using hselected,
    tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq,
    tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq⟩

/-- Squeezing between the two slowly moving endpoints forces every selector
from the central band to have `taoZ`-exponent one. -/
theorem tendsto_log_selector_div_log_taoZ_of_mem_taoSlowCentral
    {q P : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hP : ∀ᶠ x : ℕ in atTop,
      P x ∈ taoSlowCentralOneTermPrimeRange (q x) x) :
    Tendsto (fun x => Real.log (P x : ℝ) / Real.log (taoZ x))
      atTop (𝓝 1) := by
  have hlower := tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq
  have hupper := tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hP,
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hp hz
    have hpData := Finset.mem_filter.mp hp
    have hpLowerCeil := hpData.2.1
    have hpLower : taoZPowerFloor (taoSlowLowerExponent (q x)) x ≤ P x :=
      (taoZPowerFloor_le_taoOneTermExponentCutoff
        (taoSlowLowerExponent (q x)) x).trans hpLowerCeil.le
    have hpowOne : (1 : ℝ) ≤
        (taoZ x) ^ taoSlowLowerExponent (q x) :=
      Real.one_le_rpow hz.le (taoSlowLowerExponent_pos (q x)).le
    have hfloorOne : 1 ≤
        taoZPowerFloor (taoSlowLowerExponent (q x)) x := by
      exact Nat.le_floor (by simpa only [Nat.cast_one] using hpowOne)
    have hfloorPos : (0 : ℝ) <
        taoZPowerFloor (taoSlowLowerExponent (q x)) x := by
      exact_mod_cast hfloorOne
    have hpPos : (0 : ℝ) < P x := hfloorPos.trans_le (by exact_mod_cast hpLower)
    have hlog := Real.strictMonoOn_log.monotoneOn hfloorPos hpPos
      (by exact_mod_cast hpLower)
    exact div_le_div_of_nonneg_right hlog (Real.log_pos hz).le
  · filter_upwards [hP,
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hp hz
    have hpData := Finset.mem_filter.mp hp
    have hpUpper := hpData.2.2
    have hpPrime := (Finset.mem_filter.mp hpData.1).2
    have hpPos : (0 : ℝ) < P x := by exact_mod_cast hpPrime.pos
    have hcutPos : (0 : ℝ) <
        taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x :=
      hpPos.trans_le (by exact_mod_cast hpUpper)
    have hlog := Real.strictMonoOn_log.monotoneOn hpPos hcutPos
      (by exact_mod_cast hpUpper)
    exact div_le_div_of_nonneg_right hlog (Real.log_pos hz).le

/-- Every selector from a slowly diagonalized central band is in the exact
critical smooth-number regime with exponent one. -/
theorem isTaoCriticalSmoothRegime_natDiv_sq_of_mem_taoSlowCentral
    {q P : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hP : ∀ᶠ x : ℕ in atTop,
      P x ∈ taoSlowCentralOneTermPrimeRange (q x) x) :
    IsTaoCriticalSmoothRegime (fun x => x / P x ^ 2) P 1 := by
  have hPZ :=
    tendsto_log_selector_div_log_taoZ_of_mem_taoSlowCentral hq hP
  have hPsmallProduct := hPZ.mul tendsto_log_taoZ_div_log_nat_zero
  have hPsmall : Tendsto (fun x =>
      Real.log (P x : ℝ) / Real.log x) atTop (𝓝 0) := by
    have hprod0 : Tendsto (fun x =>
        (Real.log (P x : ℝ) / Real.log (taoZ x)) *
          (Real.log (taoZ x) / Real.log x)) atTop (𝓝 0) := by
      simpa using hPsmallProduct
    apply hprod0.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_gt_atTop (1 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hz hx
    have hlogz : Real.log (taoZ x) ≠ 0 := (Real.log_pos hz).ne'
    have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp
  have hPpos : ∀ᶠ x : ℕ in atTop, 0 < P x := by
    filter_upwards [hP] with x hp
    have hpData := Finset.mem_filter.mp hp
    have hpBase := Finset.mem_filter.mp hpData.1
    exact hpBase.2.pos
  exact ⟨tendsto_log_natDiv_sq_div_log_nat_one hPpos hPsmall, hPZ⟩

/-- The central mass is nonnegative. -/
theorem taoSlowCentralOneTermMass_nonneg (n x : ℕ) :
    0 ≤ taoSlowCentralOneTermMass n x := by
  unfold taoSlowCentralOneTermMass
  positivity

/-- A nonempty central range has positive mass. -/
theorem taoSlowCentralOneTermMass_pos {n x : ℕ}
    (hne : (taoSlowCentralOneTermPrimeRange n x).Nonempty) :
    0 < taoSlowCentralOneTermMass n x := by
  obtain ⟨p, hp⟩ := hne
  unfold taoSlowCentralOneTermMass
  have hone : 1 ≤ psiNat (x / p ^ 2) p := by
    have hpData := Finset.mem_filter.mp hp
    have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpData.1).1
    have hpSq : p ^ 2 ≤ x := by
      rw [pow_two]
      exact Nat.le_sqrt.mp hpRange.2
    exact one_le_psiNat (Nat.div_pos hpSq
      (pow_pos ((Finset.mem_filter.mp hpData.1).2.pos) 2))
  have hterm : (0 : ℝ) < psiNat (x / p ^ 2) p := by exact_mod_cast hone
  have hle : (psiNat (x / p ^ 2) p : ℝ) ≤
      ∑ i ∈ taoSlowCentralOneTermPrimeRange n x,
        (psiNat (x / i ^ 2) i : ℝ) :=
    Finset.single_le_sum
      (fun i _hi => show (0 : ℝ) ≤ psiNat (x / i ^ 2) i by positivity) hp
  exact hterm.trans_le hle

/-- The exact one-term identity partitions into its central and outside
prime masses. -/
theorem badOneTermCount_cast_eq_taoSlowCentral_add_outside (n x : ℕ) :
    (badOneTermCount x : ℝ) =
      taoSlowCentralOneTermMass n x + taoSlowOutsideOneTermMass n x := by
  rw [badOneTermCount_eq_sum_psiNat]
  push_cast
  unfold taoSlowCentralOneTermMass taoSlowOutsideOneTermMass
  let S : Finset ℕ := (Finset.Icc 2 x.sqrt).filter Nat.Prime
  let C : Finset ℕ := taoSlowCentralOneTermPrimeRange n x
  change (∑ p ∈ S, (psiNat (x / p ^ 2) p : ℝ)) =
    (∑ p ∈ C, (psiNat (x / p ^ 2) p : ℝ)) +
      ∑ p ∈ S \ C, (psiNat (x / p ^ 2) p : ℝ)
  have hCS : C ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  calc
    (∑ p ∈ S, (psiNat (x / p ^ 2) p : ℝ)) =
        ∑ p ∈ C ∪ (S \ C), (psiNat (x / p ^ 2) p : ℝ) := by
      rw [Finset.union_sdiff_of_subset hCS]
    _ = (∑ p ∈ C, (psiNat (x / p ^ 2) p : ℝ)) +
        ∑ p ∈ S \ C, (psiNat (x / p ^ 2) p : ℝ) :=
      Finset.sum_union Finset.disjoint_sdiff

/-! ## Fixed-row concentration outside the central band -/

/-- The exact very-small-prime part of the one-term sum. -/
noncomputable def taoVerySmallOneTermPrimeRange (x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter fun p =>
    p ≤ taoOneTermExponentCutoff (2 / 5 : ℝ) x

/-- The exact tail above the fixed exponent-three cutoff. -/
noncomputable def taoVeryLargeOneTermPrimeRange (x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter fun p =>
    taoOneTermExponentCutoff (3 : ℝ) x < p

/-- The identity ambient scale together with a rounded fixed `taoZ` power is
a critical smooth-number regime. -/
theorem isTaoCriticalSmoothRegime_self_exponentCutoff
    {β : ℝ} (hβ : 0 < β) :
    IsTaoCriticalSmoothRegime (fun x : ℕ => x)
      (taoOneTermExponentCutoff β) β := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hx
    have hlog : Real.log (x : ℝ) ≠ 0 := (Real.log_pos hx).ne'
    field_simp
  · exact tendsto_log_exponentCutoff_div_log_taoZ hβ

/-- The one-term contribution from distinguished primes at most `y` embeds
into the full `y`-smooth count. -/
theorem sum_psiNat_oneTermPrimeRange_le_psiNat
    {x y : ℕ} (hx : 1 ≤ x) :
    (∑ p ∈ ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter (fun p => p ≤ y),
        (psiNat (x / p ^ 2) p : ℝ)) ≤ (psiNat x y : ℝ) := by
  let S : Finset ℕ :=
    ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter fun p => p ≤ y
  let T : Finset ℕ := (Finset.Icc 2 (min x y)).filter Nat.Prime
  have hST : S ⊆ T := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBase := Finset.mem_filter.mp hpData.1
    have hpRange := Finset.mem_Icc.mp hpBase.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨hpRange.1, le_min (hpRange.2.trans (Nat.sqrt_le_self x)) hpData.2⟩,
        hpBase.2⟩
  have hterm : ∀ p ∈ S,
      (psiNat (x / p ^ 2) p : ℝ) ≤ (psiNat (x / p) p : ℝ) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (Finset.mem_filter.mp hpData.1).2
    have hpPow : p ≤ p ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right p hpPrime.pos
    exact_mod_cast psiNat_mono_left
      (Nat.div_le_div_left hpPow hpPrime.pos)
  calc
    (∑ p ∈ S, (psiNat (x / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ S, (psiNat (x / p) p : ℝ) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ ≤ ∑ p ∈ T, (psiNat (x / p) p : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hST
        (fun p _hp _hnot => by positivity)
    _ ≤ (psiNat x y : ℝ) := by
      rw [psiNat_eq_one_add_sum_largestPrime hx]
      push_cast
      exact le_add_of_nonneg_left (by positivity)

/-- The fixed very-small range has a power margin over the saddle exponent
two. -/
theorem eventually_sum_psiNat_taoVerySmallOneTermPrimeRange_le :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoVerySmallOneTermPrimeRange x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (12 / 5 : ℝ) := by
  have hregime := isTaoCriticalSmoothRegime_self_exponentCutoff
    (β := (2 / 5 : ℝ)) (by norm_num)
  have hsmooth := hregime.eventually_psiNat_cast_le_self_div_taoZ_rpow
    (by norm_num : (0 : ℝ) < 2 / 5) (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [hsmooth, eventually_ge_atTop (1 : ℕ)] with x hsmooth hx
  have hsum := sum_psiNat_oneTermPrimeRange_le_psiNat
    (x := x) (y := taoOneTermExponentCutoff (2 / 5 : ℝ) x) hx
  rw [show (1 / (2 / 5 : ℝ) - 1 / 10) = 12 / 5 by norm_num] at hsmooth
  simpa only [taoVerySmallOneTermPrimeRange] using hsum.trans hsmooth

/-- The exact upper shoulder between the slowly moving upper cutoff and the
fixed exponent-three cutoff. -/
noncomputable def taoSlowUpperShoulderOneTermPrimeRange
    (n x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 x.sqrt).filter Nat.Prime).filter fun p =>
    taoOneTermExponentCutoff (taoSlowUpperExponent n) x < p ∧
      p ≤ taoOneTermExponentCutoff (3 : ℝ) x

set_option maxRecDepth 4000 in
/-- At the same ambient scale, the exact lower shoulder is contained in the
fixed-row moving-grid cover. -/
theorem eventually_taoSlowSourceSmoothPrimeRange_subset_sameScale (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowSourceSmoothPrimeRange n x ⊆
        taoSlowAmbientSmoothPrimeRange n x := by
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hz
  have hlowerCut : taoOneTermExponentCutoff (39 / 100 : ℝ) x ≤
      taoOneTermExponentCutoff (2 / 5 : ℝ) x :=
    taoOneTermExponentCutoff_mono_of_one_le hz (by norm_num)
  have hupperCut :
      taoOneTermExponentCutoff (taoSlowLowerExponent n) x ≤
        taoOneTermExponentCutoff (taoSlowAmbientUpperExponent n) x :=
    taoOneTermExponentCutoff_mono_of_one_le hz
      (taoSlowLowerExponent_lt_ambient n).le
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpExpanded : p ∈ taoOneTermExponentPrimeBand
      (39 / 100 : ℝ) (taoSlowAmbientUpperExponent n) x :=
    Finset.mem_filter.mpr
      ⟨hpData.1, lt_of_le_of_lt hlowerCut hpData.2.1,
        hpData.2.2.trans hupperCut⟩
  rw [taoSlowAmbientSmoothPrimeRange]
  by_cases hpHalf : p ≤ taoOneTermExponentCutoff (1 / 2 : ℝ) x
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨hpData.1, (Finset.mem_filter.mp hpExpanded).2.1, hpHalf⟩
  · apply Finset.mem_union_right
    rw [taoSlowGridPrimeUnion]
    have hpGridBand : p ∈ taoOneTermExponentPrimeBand
        (taoOneTermGridExponent (taoSlowGridSize n) 0)
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowGridStop n)) x := by
      rw [taoOneTermGridExponent_zero,
        taoOneTermGridExponent_slowGridStop n]
      exact Finset.mem_filter.mpr
        ⟨hpData.1, Nat.lt_of_not_ge hpHalf,
          (Finset.mem_filter.mp hpExpanded).2.2⟩
    have hcovered := exponentPrimeBand_gridEndpoints_subset_biUnion
      (K := taoSlowGridSize n) (lo := 0) (hi := taoSlowGridStop n)
      (X := x) (taoSlowGridStop_pos n) hpGridBand
    rw [Finset.mem_biUnion] at hcovered ⊢
    obtain ⟨k, hk, hpk⟩ := hcovered
    exact ⟨k, by simpa only [taoSlowGridIndices, Finset.mem_range] using
      (Finset.mem_Ico.mp hk).2, hpk⟩

/-- The exact upper shoulder is contained in the fixed-row high-prime grid
at the same ambient scale. -/
theorem eventually_taoSlowUpperShoulder_subset_ambient (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowUpperShoulderOneTermPrimeRange n x ⊆
        taoSlowAmbientHighPrimeRange n x := by
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hz
  have hlowerCut :
      taoOneTermExponentCutoff (taoSlowAmbientLowerExponent n) x ≤
        taoOneTermExponentCutoff (taoSlowUpperExponent n) x :=
    taoOneTermExponentCutoff_mono_of_one_le hz
      (taoSlowAmbientLowerExponent_lt_upper n).le
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpExpanded : p ∈ taoOneTermExponentPrimeBand
      (taoSlowAmbientLowerExponent n) (3 : ℝ) x :=
    Finset.mem_filter.mpr
      ⟨hpData.1, lt_of_le_of_lt hlowerCut hpData.2.1,
        hpData.2.2⟩
  rw [taoSlowAmbientHighPrimeRange]
  by_cases hpTwo : p ≤ taoOneTermExponentCutoff (2 : ℝ) x
  · apply Finset.mem_union_left
    rw [taoSlowHighGridPrimeUnion]
    have hpGridBand : p ∈ taoOneTermExponentPrimeBand
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowHighGridStart n))
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowGridSize n)) x := by
      rw [taoOneTermGridExponent_slowHighGridStart n,
        taoOneTermGridExponent_self (taoSlowGridSize_pos n)]
      exact Finset.mem_filter.mpr
        ⟨hpData.1, (Finset.mem_filter.mp hpExpanded).2.1, hpTwo⟩
    exact exponentPrimeBand_gridEndpoints_subset_biUnion
      (taoSlowHighGridStart_lt_gridSize n) hpGridBand
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨hpData.1, Nat.lt_of_not_ge hpTwo,
        (Finset.mem_filter.mp hpExpanded).2.2⟩

/-- Fixed-row bound for the exact lower shoulder. -/
theorem eventually_sum_psiNat_taoSlowSourceSmoothPrimeRange_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoSlowSourceSmoothPrimeRange n x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        ((taoSlowGridStop n : ℝ) + 1) *
          ((x : ℝ) / (taoZ x) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
  filter_upwards [eventually_taoSlowSourceSmoothPrimeRange_subset_sameScale n,
    eventually_sum_psiNat_slowAmbientSmoothPrimeRange_le n] with
      x hsubset hsum
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p _hp _hnot => by positivity)).trans hsum

/-- Fixed-row bound for the exact upper shoulder. -/
theorem eventually_sum_psiNat_taoSlowUpperShoulder_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoSlowUpperShoulderOneTermPrimeRange n x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1) *
          ((x : ℝ) / (taoZ x) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
  filter_upwards [eventually_taoSlowUpperShoulder_subset_ambient n,
    eventually_sum_psiNat_slowAmbientHighPrimeRange_le n] with
      x hsubset hsum
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun p _hp _hnot => by positivity)).trans hsum

/-- Reciprocal-square estimate for the exact exponent-three tail. -/
theorem sum_psiNat_taoVeryLargeOneTermPrimeRange_le
    {x : ℕ} (hcut : 2 ≤ taoOneTermExponentCutoff (3 : ℝ) x) :
    (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
      (x : ℝ) /
        ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) := by
  have hsubset : taoVeryLargeOneTermPrimeRange x ⊆
      Finset.Icc (taoOneTermExponentCutoff (3 : ℝ) x) x.sqrt := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr
      ⟨hpData.2.le, (Finset.mem_Icc.mp
        (Finset.mem_filter.mp hpData.1).1).2⟩
  calc
    (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ taoVeryLargeOneTermPrimeRange x,
          (x : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        (psiNat (x / p ^ 2) p : ℝ) ≤ (x / p ^ 2 : ℕ) := by
          exact_mod_cast psiNat_le_self (x / p ^ 2) p
        _ ≤ (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (x : ℝ) / (p : ℝ) ^ 2 := by simp only [Nat.cast_pow]
    _ ≤ ∑ p ∈ Finset.Icc (taoOneTermExponentCutoff (3 : ℝ) x) x.sqrt,
          (x : ℝ) / (p : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _hp _hnot => by positivity)
    _ = (x : ℝ) *
        (∑ p ∈ Finset.Icc (taoOneTermExponentCutoff (3 : ℝ) x) x.sqrt,
          (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ (x : ℝ) *
        (1 / ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_one_div_nat_sq_le hcut) (by positivity)
    _ = (x : ℝ) /
        ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) := by ring

/-- The exponent-three reciprocal-square tail has a fixed half-power margin
over the saddle exponent two. -/
theorem eventually_sum_psiNat_taoVeryLargeOneTermPrimeRange_le :
    ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
          (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) / (taoZ x) ^ (5 / 2 : ℝ) := by
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (4 : ℝ))] with x hz
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hzCubeTwo : (2 : ℝ) ≤ (taoZ x) ^ (3 : ℕ) := by
    norm_num [pow_succ]
    nlinarith
  have hcutReal : (taoZ x) ^ (3 : ℕ) ≤
      (taoOneTermExponentCutoff (3 : ℝ) x : ℝ) := by
    unfold taoOneTermExponentCutoff
    norm_num [Real.rpow_natCast]
    exact Nat.le_ceil _
  have hcut : 2 ≤ taoOneTermExponentCutoff (3 : ℝ) x := by
    exact_mod_cast hzCubeTwo.trans hcutReal
  have hcutSub : (taoZ x) ^ (3 : ℕ) / 2 ≤
      ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤
      taoOneTermExponentCutoff (3 : ℝ) x), Nat.cast_one]
    nlinarith
  have hdenPos : 0 <
      ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 <
      taoOneTermExponentCutoff (3 : ℝ) x - 1)
  have hzCubePos : 0 < (taoZ x) ^ (3 : ℕ) := by positivity
  have htail := sum_psiNat_taoVeryLargeOneTermPrimeRange_le
    (x := x) hcut
  calc
    (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) ≤
        (x : ℝ) /
          ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) := htail
    _ ≤ 2 * (x : ℝ) / (taoZ x) ^ (3 : ℕ) := by
      have hfrac :
          1 / ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) ≤
            2 / (taoZ x) ^ (3 : ℕ) := by
        rw [div_le_div_iff₀ hdenPos hzCubePos]
        nlinarith
      calc
        (x : ℝ) /
            ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ) =
          (x : ℝ) *
            (1 / ((taoOneTermExponentCutoff (3 : ℝ) x - 1 : ℕ) : ℝ)) := by
              ring
        _ ≤ (x : ℝ) * (2 / (taoZ x) ^ (3 : ℕ)) := by gcongr
        _ = 2 * (x : ℝ) / (taoZ x) ^ (3 : ℕ) := by ring
    _ ≤ (x : ℝ) / (taoZ x) ^ (5 / 2 : ℝ) := by
      have hsqrt : (2 : ℝ) ≤ (taoZ x) ^ (1 / 2 : ℝ) := by
        rw [show (taoZ x) ^ (1 / 2 : ℝ) = Real.sqrt (taoZ x) by
          rw [Real.sqrt_eq_rpow]]
        rw [Real.le_sqrt (by norm_num) hzPos.le]
        norm_num
        exact hz
      have hfactor : 2 / (taoZ x) ^ (3 : ℕ) ≤
          1 / (taoZ x) ^ (5 / 2 : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [one_mul]
        calc
          2 * (taoZ x) ^ (5 / 2 : ℝ) ≤
              (taoZ x) ^ (1 / 2 : ℝ) *
                (taoZ x) ^ (5 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hsqrt
              (Real.rpow_nonneg hzPos.le _)
          _ = (taoZ x) ^ (3 : ℝ) := by
            rw [← Real.rpow_add hzPos]
            congr 1
            ring
          _ = (taoZ x) ^ (3 : ℕ) := by
            norm_num [Real.rpow_natCast]
      calc
        2 * (x : ℝ) / (taoZ x) ^ (3 : ℕ) =
            (x : ℝ) * (2 / (taoZ x) ^ (3 : ℕ)) := by ring
        _ ≤ (x : ℝ) * (1 / (taoZ x) ^ (5 / 2 : ℝ)) := by gcongr
        _ = (x : ℝ) / (taoZ x) ^ (5 / 2 : ℝ) := by ring

/-- Four explicit ranges covering the complement of the moving central
packet. -/
noncomputable def taoSlowOutsideOneTermPrimeCover (n x : ℕ) : Finset ℕ :=
  taoVerySmallOneTermPrimeRange x ∪
    (taoSlowSourceSmoothPrimeRange n x ∪
      (taoSlowUpperShoulderOneTermPrimeRange n x ∪
        taoVeryLargeOneTermPrimeRange x))

theorem taoSlowOutsideOneTermPrimeRange_subset_cover (n x : ℕ) :
    ((Finset.Icc 2 x.sqrt).filter Nat.Prime) \
        taoSlowCentralOneTermPrimeRange n x ⊆
      taoSlowOutsideOneTermPrimeCover n x := by
  intro p hp
  have hpBase := (Finset.mem_sdiff.mp hp).1
  have hpOutside := (Finset.mem_sdiff.mp hp).2
  by_cases hlower :
      p ≤ taoOneTermExponentCutoff (taoSlowLowerExponent n) x
  · by_cases hsmall : p ≤ taoOneTermExponentCutoff (2 / 5 : ℝ) x
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hpBase, hsmall⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨hpBase, Nat.lt_of_not_ge hsmall, hlower⟩
  · have haboveLower :
        taoOneTermExponentCutoff (taoSlowLowerExponent n) x < p :=
      Nat.lt_of_not_ge hlower
    by_cases hupper :
        p ≤ taoOneTermExponentCutoff (taoSlowUpperExponent n) x
    · exact (hpOutside (Finset.mem_filter.mpr
        ⟨hpBase, haboveLower, hupper⟩)).elim
    · have haboveUpper :
          taoOneTermExponentCutoff (taoSlowUpperExponent n) x < p :=
        Nat.lt_of_not_ge hupper
      by_cases hthree : p ≤ taoOneTermExponentCutoff (3 : ℝ) x
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr
          ⟨hpBase, haboveUpper, hthree⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr
          ⟨hpBase, Nat.lt_of_not_ge hthree⟩

/-- Outside mass bounded by the four explicit complement pieces. -/
theorem taoSlowOutsideOneTermMass_le_four_sums (n x : ℕ) :
    taoSlowOutsideOneTermMass n x ≤
      (∑ p ∈ taoVerySmallOneTermPrimeRange x,
        (psiNat (x / p ^ 2) p : ℝ)) +
        ((∑ p ∈ taoSlowSourceSmoothPrimeRange n x,
          (psiNat (x / p ^ 2) p : ℝ)) +
          ((∑ p ∈ taoSlowUpperShoulderOneTermPrimeRange n x,
            (psiNat (x / p ^ 2) p : ℝ)) +
            (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
              (psiNat (x / p ^ 2) p : ℝ)))) := by
  let f : ℕ → ℝ := fun p => (psiNat (x / p ^ 2) p : ℝ)
  calc
    taoSlowOutsideOneTermMass n x ≤
        ∑ p ∈ taoSlowOutsideOneTermPrimeCover n x, f p := by
      unfold taoSlowOutsideOneTermMass
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoSlowOutsideOneTermPrimeRange_subset_cover n x)
        (fun p _hp _hnot => by positivity)
    _ ≤ (∑ p ∈ taoVerySmallOneTermPrimeRange x, f p) +
        ∑ p ∈ taoSlowSourceSmoothPrimeRange n x ∪
          (taoSlowUpperShoulderOneTermPrimeRange n x ∪
            taoVeryLargeOneTermPrimeRange x), f p := by
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)
    _ ≤ (∑ p ∈ taoVerySmallOneTermPrimeRange x, f p) +
        ((∑ p ∈ taoSlowSourceSmoothPrimeRange n x, f p) +
          ∑ p ∈ taoSlowUpperShoulderOneTermPrimeRange n x ∪
            taoVeryLargeOneTermPrimeRange x, f p) := by
      gcongr
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)
    _ ≤ (∑ p ∈ taoVerySmallOneTermPrimeRange x, f p) +
        ((∑ p ∈ taoSlowSourceSmoothPrimeRange n x, f p) +
          ((∑ p ∈ taoSlowUpperShoulderOneTermPrimeRange n x, f p) +
            ∑ p ∈ taoVeryLargeOneTermPrimeRange x, f p)) := by
      gcongr
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)

/-- Fixed coefficient left after adding the four complement estimates in one
slow-cutoff row. -/
noncomputable def taoSlowOutsideOneTermCoefficient (n : ℕ) : ℝ :=
  2 + ((taoSlowGridStop n : ℝ) + 1) +
    (((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1)

theorem taoSlowOutsideOneTermCoefficient_pos (n : ℕ) :
    0 < taoSlowOutsideOneTermCoefficient n := by
  unfold taoSlowOutsideOneTermCoefficient
  positivity

/-- For each fixed row, all prime mass outside the central band gains a
positive power of `taoZ` over the main saddle exponent two. -/
theorem eventually_taoSlowOutsideOneTermMass_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowOutsideOneTermMass n x ≤
        taoSlowOutsideOneTermCoefficient n *
          ((x : ℝ) / (taoZ x) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
  let δ : ℝ := 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  let A : ℝ := (taoSlowGridStop n : ℝ) + 1
  let B : ℝ :=
    ((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by positivity
  have hδSmall : δ ≤ 2 / 5 := by
    dsimp only [δ]
    have hdSq : (100 : ℝ) ≤ (taoSlowCutoffDenominator n : ℝ) ^ 2 := by
      nlinarith
    have hden : (0 : ℝ) <
        8 * (taoSlowCutoffDenominator n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hδLarge : δ ≤ 1 / 2 := hδSmall.trans (by norm_num)
  filter_upwards [eventually_sum_psiNat_taoVerySmallOneTermPrimeRange_le,
    eventually_sum_psiNat_taoSlowSourceSmoothPrimeRange_le n,
    eventually_sum_psiNat_taoSlowUpperShoulder_le n,
    eventually_sum_psiNat_taoVeryLargeOneTermPrimeRange_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hsmall hlower hupper hlarge hz
  let T : ℝ := (x : ℝ) / (taoZ x) ^ (2 + δ)
  have hsmallT : (x : ℝ) / (taoZ x) ^ (12 / 5 : ℝ) ≤ T := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hz
      (show 2 + δ ≤ 12 / 5 by linarith)
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (taoZ_pos x) _) hpow
  have hlargeT : (x : ℝ) / (taoZ x) ^ (5 / 2 : ℝ) ≤ T := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hz
      (show 2 + δ ≤ 5 / 2 by linarith)
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (taoZ_pos x) _) hpow
  have hout := taoSlowOutsideOneTermMass_le_four_sums n x
  calc
    taoSlowOutsideOneTermMass n x ≤
        (∑ p ∈ taoVerySmallOneTermPrimeRange x,
          (psiNat (x / p ^ 2) p : ℝ)) +
          ((∑ p ∈ taoSlowSourceSmoothPrimeRange n x,
            (psiNat (x / p ^ 2) p : ℝ)) +
            ((∑ p ∈ taoSlowUpperShoulderOneTermPrimeRange n x,
              (psiNat (x / p ^ 2) p : ℝ)) +
              (∑ p ∈ taoVeryLargeOneTermPrimeRange x,
                (psiNat (x / p ^ 2) p : ℝ)))) := hout
    _ ≤ T + (A * T + (B * T + T)) := by
      exact add_le_add (hsmall.trans hsmallT)
        (add_le_add (by simpa only [A, T, δ] using hlower)
          (add_le_add (by simpa only [B, T, δ] using hupper)
            (hlarge.trans hlargeT)))
    _ = taoSlowOutsideOneTermCoefficient n *
        ((x : ℝ) / (taoZ x) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
      simp only [taoSlowOutsideOneTermCoefficient, T, A, B, δ]
      ring

/-- In every fixed slow-cutoff row, the outside mass is negligible relative
to the complete one-term count. -/
theorem tendsto_taoSlowOutsideOneTermMass_div_badOneTermCount_zero
    (n : ℕ) :
    Tendsto (fun x =>
      taoSlowOutsideOneTermMass n x / (badOneTermCount x : ℝ))
      atTop (𝓝 0) := by
  let δ : ℝ := 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  let η : ℝ := δ / 2
  let C : ℝ := taoSlowOutsideOneTermCoefficient n
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hpowTop : Tendsto (fun x : ℕ => (taoZ x) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_taoZ_atTop
  have hupperZero : Tendsto (fun x : ℕ => C / (taoZ x) ^ η)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
      tendsto_const_nhds
    simpa using hconst.div_atTop hpowTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hupperZero
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with x hx
    exact div_nonneg (by unfold taoSlowOutsideOneTermMass; positivity)
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_taoSlowOutsideOneTermMass_le n,
      eventually_self_div_taoZ_rpow_le_badOneTermCount hη,
      eventually_ge_atTop (4 : ℕ)] with x hout hlower hx
    have hdenPos : (0 : ℝ) < badOneTermCount x := by
      exact_mod_cast one_le_badOneTermCount hx
    have hscaleNonneg : 0 ≤
        (x : ℝ) / (taoZ x) ^ (2 + η) :=
      div_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (taoZ_pos x).le _)
    have hfactorNonneg : 0 ≤ C / (taoZ x) ^ η := by
      exact div_nonneg (taoSlowOutsideOneTermCoefficient_pos n).le
        (Real.rpow_nonneg (taoZ_pos x).le _)
    rw [div_le_iff₀ hdenPos]
    calc
      taoSlowOutsideOneTermMass n x ≤
          C * ((x : ℝ) / (taoZ x) ^ (2 + δ)) := by
        simpa only [C, δ] using hout
      _ = (C / (taoZ x) ^ η) *
          ((x : ℝ) / (taoZ x) ^ (2 + η)) := by
        have hzPos := taoZ_pos x
        have hexponent : 2 + δ = η + (2 + η) := by
          dsimp only [η]
          ring
        rw [hexponent, Real.rpow_add hzPos]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hzPos η),
          ne_of_gt (Real.rpow_pos_of_pos hzPos (2 + η))]
      _ ≤ (C / (taoZ x) ^ η) * (badOneTermCount x : ℝ) :=
        mul_le_mul_of_nonneg_left hlower hfactorNonneg

/-- A single slowly increasing row retains a nonempty central band and makes
its complementary mass `o(B¹(x))`. -/
theorem exists_taoSlowCentralConcentrationDiagonal :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      (∀ᶠ x : ℕ in atTop,
        (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) ∧
      Tendsto (fun x =>
        taoSlowOutsideOneTermMass (q x) x /
          (badOneTermCount x : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) := by
  let P : ℕ → ℕ → Prop := fun n x =>
    (taoSlowCentralOneTermPrimeRange n x).Nonempty ∧
      taoSlowOutsideOneTermMass n x / (badOneTermCount x : ℝ) ≤
        (1 : ℝ) / (n + 1 : ℕ)
  have hP : ∀ n, ∀ᶠ x : ℕ in atTop, P n x := by
    intro n
    have hsmall : ∀ᶠ x : ℕ in atTop,
        taoSlowOutsideOneTermMass n x / (badOneTermCount x : ℝ) ≤
          (1 : ℝ) / (n + 1 : ℕ) := by
      have hlim :=
        tendsto_taoSlowOutsideOneTermMass_div_badOneTermCount_zero n
      have htarget : (0 : ℝ) < 1 / (n + 1 : ℕ) := by positivity
      exact (hlim.eventually (Iio_mem_nhds htarget)).mono fun _ hx => hx.le
    filter_upwards [eventually_taoSlowCentralOneTermPrimeRange_nonempty n,
      hsmall] with x hne hbound
    exact ⟨hne, hbound⟩
  obtain ⟨q, hq, hselected⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  have hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty :=
    hselected.mono fun _ hx => hx.1
  have hbound : ∀ᶠ x : ℕ in atTop,
      taoSlowOutsideOneTermMass (q x) x / (badOneTermCount x : ℝ) ≤
        (1 : ℝ) / (q x + 1 : ℕ) :=
    hselected.mono fun _ hx => hx.2
  have hqSucc : Tendsto (fun x => q x + 1) atTop atTop := by
    rw [tendsto_atTop_atTop] at hq ⊢
    intro b
    obtain ⟨a, ha⟩ := hq b
    exact ⟨a, fun x hx => (ha x hx).trans (Nat.le_add_right (q x) 1)⟩
  have hqSuccReal : Tendsto (fun x => ((q x + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqSucc
  have honeDiv : Tendsto (fun x => (1 : ℝ) / (q x + 1 : ℕ))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).div_atTop hqSuccReal
  have houtNonneg : ∀ᶠ x : ℕ in atTop,
      0 ≤ taoSlowOutsideOneTermMass (q x) x /
        (badOneTermCount x : ℝ) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with x hx
    exact div_nonneg (by unfold taoSlowOutsideOneTermMass; positivity)
      (Nat.cast_nonneg _)
  have hout : Tendsto (fun x =>
      taoSlowOutsideOneTermMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      honeDiv houtNonneg hbound
  exact ⟨q, hq, hne, hout,
    tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq,
    tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq⟩

/-- Along the concentrating diagonal, the central packet carries asymptotic
mass one relative to the full one-term count. -/
theorem tendsto_taoSlowCentralOneTermMass_div_badOneTermCount_one
    {q : ℕ → ℕ}
    (hout : Tendsto (fun x =>
      taoSlowOutsideOneTermMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun x =>
      taoSlowCentralOneTermMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 1) := by
  have htarget :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hout
  have htarget' : Tendsto (fun x =>
      1 - taoSlowOutsideOneTermMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 1) := by
    simpa using htarget
  apply htarget'.congr'
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with x hx
  have hden : (badOneTermCount x : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (one_le_badOneTermCount hx)).ne'
  have hpartition := badOneTermCount_cast_eq_taoSlowCentral_add_outside
    (q x) x
  field_simp
  linarith

/-- Natural dilation by one half is natural division by two. -/
theorem taoNaturalDilation_half (x : ℕ) :
    taoNaturalDilation (1 / 2 : ℝ) x = x / 2 := by
  unfold taoNaturalDilation
  rw [show (1 / 2 : ℝ) * (x : ℝ) = (x : ℝ) / (2 : ℕ) by ring]
  rw [Nat.floor_div_natCast, Nat.floor_natCast]

/-- Under the sharp critical formula, halving the cofactor cutoff halves the
entire slowly diagonalized central packet. -/
theorem tendsto_taoSlowCentralOneTermHalvedMass_div
    (hlimit : TaoCriticalSmoothDilationLimitConclusion)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) :
    Tendsto (fun x =>
      taoSlowCentralOneTermHalvedMass (q x) x /
        taoSlowCentralOneTermMass (q x) x) atTop (𝓝 (1 / 2 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huniform : ∀ᶠ x : ℕ in atTop,
      ∀ p, p ∈ taoSlowCentralOneTermPrimeRange (q x) x →
        1 / 2 - ε <
            (psiNat ((x / 2) / p ^ 2) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) ∧
          (psiNat ((x / 2) / p ^ 2) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) < 1 / 2 + ε := by
    apply eventually_forall_of_forall_selector
      (R := fun x p => p ∈ taoSlowCentralOneTermPrimeRange (q x) x)
      (P := fun x p =>
        1 / 2 - ε <
            (psiNat ((x / 2) / p ^ 2) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) ∧
          (psiNat ((x / 2) / p ^ 2) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) < 1 / 2 + ε)
    · filter_upwards [hne] with x hx
      exact hx
    · intro P hP
      have hregime :=
        isTaoCriticalSmoothRegime_natDiv_sq_of_mem_taoSlowCentral hq hP
      have hratio := hlimit (1 / 2) 1 (fun x => x / P x ^ 2) P
        (by norm_num) (by norm_num) hregime
      have hnear := hratio.eventually
        (Ioo_mem_nhds
          (show 1 / 2 - ε < (1 / 2 : ℝ) by linarith)
          (show (1 / 2 : ℝ) < 1 / 2 + ε by linarith))
      simpa only [taoNaturalDilation_half, Nat.div_div_eq_div_mul,
        Nat.mul_comm] using hnear
  rw [eventually_atTop] at hne huniform
  obtain ⟨N₁, hN₁⟩ := hne
  obtain ⟨N₂, hN₂⟩ := huniform
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  have hnonempty := hN₁ x ((Nat.le_max_left _ _).trans hx)
  have hbounds := hN₂ x ((Nat.le_max_right _ _).trans hx)
  have hdenPos : 0 < taoSlowCentralOneTermMass (q x) x :=
    taoSlowCentralOneTermMass_pos hnonempty
  have hlower : (1 / 2 - ε) * taoSlowCentralOneTermMass (q x) x <
      taoSlowCentralOneTermHalvedMass (q x) x := by
    unfold taoSlowCentralOneTermMass taoSlowCentralOneTermHalvedMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact hnonempty
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpData.1).1
      have hpSq : p ^ 2 ≤ x := by
        rw [pow_two]
        exact Nat.le_sqrt.mp hpRange.2
      have hpsiPos : (0 : ℝ) < psiNat (x / p ^ 2) p := by
        exact_mod_cast one_le_psiNat
          (Nat.div_pos hpSq
            (pow_pos (Finset.mem_filter.mp hpData.1).2.pos 2))
      exact (lt_div_iff₀ hpsiPos).mp (hbounds p hp).1
  have hupper : taoSlowCentralOneTermHalvedMass (q x) x <
      (1 / 2 + ε) * taoSlowCentralOneTermMass (q x) x := by
    unfold taoSlowCentralOneTermMass taoSlowCentralOneTermHalvedMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact hnonempty
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpData.1).1
      have hpSq : p ^ 2 ≤ x := by
        rw [pow_two]
        exact Nat.le_sqrt.mp hpRange.2
      have hpsiPos : (0 : ℝ) < psiNat (x / p ^ 2) p := by
        exact_mod_cast one_le_psiNat
          (Nat.div_pos hpSq
            (pow_pos (Finset.mem_filter.mp hpData.1).2.pos 2))
      exact (div_lt_iff₀ hpsiPos).mp (hbounds p hp).2
  rw [Real.dist_eq]
  rw [abs_lt]
  have hratioLower : 1 / 2 - ε <
      taoSlowCentralOneTermHalvedMass (q x) x /
        taoSlowCentralOneTermMass (q x) x :=
    (lt_div_iff₀ hdenPos).2 hlower
  have hratioUpper :
      taoSlowCentralOneTermHalvedMass (q x) x /
          taoSlowCentralOneTermMass (q x) x < 1 / 2 + ε :=
    (div_lt_iff₀ hdenPos).2 hupper
  constructor
  · linarith only [hratioLower]
  · linarith only [hratioUpper]

/-- Every prime in the slowly diagonalized central band has square at most
half the ambient cutoff, uniformly for large ambient cutoffs. -/
theorem eventually_taoSlowCentralOneTermPrimeRange_sq_le_half
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ taoSlowCentralOneTermPrimeRange (q x) x,
      p ^ 2 ≤ x / 2 := by
  apply eventually_forall_of_forall_selector
    (R := fun x p => p ∈ taoSlowCentralOneTermPrimeRange (q x) x)
    (P := fun x p => p ^ 2 ≤ x / 2)
  · filter_upwards [hne] with x hx
    exact hx
  · intro P hP
    have hregime :=
      isTaoCriticalSmoothRegime_natDiv_sq_of_mem_taoSlowCentral hq hP
    filter_upwards [hregime.eventually_two_le_X, hP] with x hx hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (Finset.mem_filter.mp hpData.1).2
    have hmul : 2 * P x ^ 2 ≤ x :=
      (Nat.le_div_iff_mul_le (pow_pos hpPrime.pos 2)).mp hx
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    simpa only [Nat.mul_comm] using hmul

/-- The halved central packet is part of the exact one-term count at the
halved ambient cutoff. -/
theorem eventually_taoSlowCentralOneTermHalvedMass_le_badOneTermCount_half
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowCentralOneTermHalvedMass (q x) x ≤
        (badOneTermCount (x / 2) : ℝ) := by
  filter_upwards [eventually_taoSlowCentralOneTermPrimeRange_sq_le_half
    hq hne] with x hsq
  rw [badOneTermCount_eq_sum_psiNat]
  push_cast
  unfold taoSlowCentralOneTermHalvedMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBase := Finset.mem_filter.mp hpData.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hpBase.1).1,
          Nat.le_sqrt.mpr (by simpa only [pow_two] using hsq p hp)⟩,
        hpBase.2⟩
  · intro p _hp _hnot
    positivity

/-- The count at the halved cutoff is bounded by the halved central packet
plus the outside mass at the original cutoff. -/
theorem eventually_badOneTermCount_half_le_taoSlowCentralHalved_add_outside
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) :
    ∀ᶠ x : ℕ in atTop,
      (badOneTermCount (x / 2) : ℝ) ≤
        taoSlowCentralOneTermHalvedMass (q x) x +
          taoSlowOutsideOneTermMass (q x) x := by
  filter_upwards [eventually_taoSlowCentralOneTermPrimeRange_sq_le_half
    hq hne] with x hsq
  let S₀ : Finset ℕ := (Finset.Icc 2 (x / 2).sqrt).filter Nat.Prime
  let S : Finset ℕ := (Finset.Icc 2 x.sqrt).filter Nat.Prime
  let C : Finset ℕ := taoSlowCentralOneTermPrimeRange (q x) x
  have hCS₀ : C ⊆ S₀ := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBase := Finset.mem_filter.mp hpData.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hpBase.1).1,
          Nat.le_sqrt.mpr (by simpa only [pow_two] using hsq p hp)⟩,
        hpBase.2⟩
  have hS₀S : S₀ ⊆ S := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpRange := Finset.mem_Icc.mp hpData.1
    have hpSqHalf : p * p ≤ x / 2 := Nat.le_sqrt.mp hpRange.2
    have hpSq : p * p ≤ x := hpSqHalf.trans (Nat.div_le_self x 2)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpRange.1, Nat.le_sqrt.mpr hpSq⟩, hpData.2⟩
  have houtsideSubset : S₀ \ C ⊆ S \ C := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨hS₀S (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
  have houtsideTerm :
      (∑ p ∈ S₀ \ C, (psiNat ((x / 2) / p ^ 2) p : ℝ)) ≤
        ∑ p ∈ S \ C, (psiNat (x / p ^ 2) p : ℝ) := by
    calc
      (∑ p ∈ S₀ \ C, (psiNat ((x / 2) / p ^ 2) p : ℝ)) ≤
          ∑ p ∈ S₀ \ C, (psiNat (x / p ^ 2) p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact_mod_cast psiNat_mono_left
          (Nat.div_le_div_right (Nat.div_le_self x 2))
      _ ≤ ∑ p ∈ S \ C, (psiNat (x / p ^ 2) p : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg houtsideSubset
          (fun p _hp _hnot => by positivity)
  rw [badOneTermCount_eq_sum_psiNat]
  push_cast
  change (∑ p ∈ S₀, (psiNat ((x / 2) / p ^ 2) p : ℝ)) ≤
    taoSlowCentralOneTermHalvedMass (q x) x +
      taoSlowOutsideOneTermMass (q x) x
  calc
    (∑ p ∈ S₀, (psiNat ((x / 2) / p ^ 2) p : ℝ)) =
        ∑ p ∈ C ∪ (S₀ \ C),
          (psiNat ((x / 2) / p ^ 2) p : ℝ) := by
      rw [Finset.union_sdiff_of_subset hCS₀]
    _ = (∑ p ∈ C, (psiNat ((x / 2) / p ^ 2) p : ℝ)) +
        ∑ p ∈ S₀ \ C, (psiNat ((x / 2) / p ^ 2) p : ℝ) :=
      Finset.sum_union Finset.disjoint_sdiff
    _ ≤ (∑ p ∈ C, (psiNat ((x / 2) / p ^ 2) p : ℝ)) +
        ∑ p ∈ S \ C, (psiNat (x / p ^ 2) p : ℝ) :=
      add_le_add le_rfl houtsideTerm
    _ = taoSlowCentralOneTermHalvedMass (q x) x +
        taoSlowOutsideOneTermMass (q x) x := by
      rfl

/-- The halved central packet has limiting mass one half relative to the full
one-term count at the original scale. -/
theorem tendsto_taoSlowCentralOneTermHalvedMass_div_badOneTermCount_half
    (hlimit : TaoCriticalSmoothDilationLimitConclusion)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty)
    (hout : Tendsto (fun x =>
      taoSlowOutsideOneTermMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun x =>
      taoSlowCentralOneTermHalvedMass (q x) x /
        (badOneTermCount x : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hhalf := tendsto_taoSlowCentralOneTermHalvedMass_div hlimit hq hne
  have hcentral :=
    tendsto_taoSlowCentralOneTermMass_div_badOneTermCount_one hout
  have hproduct := hhalf.mul hcentral
  have hproduct' : Tendsto (fun x =>
      (taoSlowCentralOneTermHalvedMass (q x) x /
          taoSlowCentralOneTermMass (q x) x) *
        (taoSlowCentralOneTermMass (q x) x /
          (badOneTermCount x : ℝ))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [hne, eventually_ge_atTop (4 : ℕ)] with x hneX hx
  have hcentralNe : taoSlowCentralOneTermMass (q x) x ≠ 0 :=
    (taoSlowCentralOneTermMass_pos hneX).ne'
  have hbadNe : (badOneTermCount x : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (one_le_badOneTermCount hx)).ne'
  field_simp

/-- The complete one-term count is regularly varying under halving. -/
theorem tendsto_badOneTermCount_half_div_self
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    Tendsto (fun x =>
      (badOneTermCount (x / 2) : ℝ) / (badOneTermCount x : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨q, hq, hne, hout, _hlower, _hupper⟩ :=
    exists_taoSlowCentralConcentrationDiagonal
  have hhalf :=
    tendsto_taoSlowCentralOneTermHalvedMass_div_badOneTermCount_half
      hlimit hq hne hout
  have hupperLim := hhalf.add hout
  have hupperLim' : Tendsto (fun x =>
      taoSlowCentralOneTermHalvedMass (q x) x /
          (badOneTermCount x : ℝ) +
        taoSlowOutsideOneTermMass (q x) x /
          (badOneTermCount x : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hupperLim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hhalf hupperLim'
  · filter_upwards [
      eventually_taoSlowCentralOneTermHalvedMass_le_badOneTermCount_half hq hne,
      eventually_ge_atTop (4 : ℕ)] with x hlower hx
    have hdenPos : (0 : ℝ) < badOneTermCount x := by
      exact_mod_cast one_le_badOneTermCount hx
    exact div_le_div_of_nonneg_right hlower hdenPos.le
  · filter_upwards [
      eventually_badOneTermCount_half_le_taoSlowCentralHalved_add_outside
        hq hne,
      eventually_ge_atTop (4 : ℕ)] with x hupper hx
    have hdenPos : (0 : ℝ) < badOneTermCount x := by
      exact_mod_cast one_le_badOneTermCount hx
    have hdiv := div_le_div_of_nonneg_right hupper hdenPos.le
    simpa only [add_div] using hdiv

/-! ## All fixed dilations and Lemma 1.6(ii) -/

/-- The half-ratio is eventually bounded below by `1/4`, so the full count
at `x` is at most four times the count at the floored half endpoint. -/
theorem eventually_badOneTermCount_le_four_mul_half
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    ∀ᶠ x : ℕ in atTop,
      badOneTermCount x ≤ 4 * badOneTermCount (x / 2) := by
  have hhalf := tendsto_badOneTermCount_half_div_self hlimit
  have hlower : ∀ᶠ x : ℕ in atTop,
      (1 / 4 : ℝ) <
        (badOneTermCount (x / 2) : ℝ) / (badOneTermCount x : ℝ) :=
    hhalf.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hlower, eventually_ge_atTop (4 : ℕ)] with x hx hX
  have hdenPos : (0 : ℝ) < badOneTermCount x := by
    exact_mod_cast one_le_badOneTermCount hX
  have hmul : (1 / 4 : ℝ) * badOneTermCount x <
      badOneTermCount (x / 2) :=
    (lt_div_iff₀ hdenPos).mp hx
  exact_mod_cast (show (badOneTermCount x : ℝ) ≤
      4 * badOneTermCount (x / 2) by linarith)

/-- Iterating the one-step half comparison controls every fixed power-of-two
contraction, with an explicit (deliberately coarse) factor `4^k`. -/
theorem eventually_badOneTermCount_le_four_pow_mul_div_pow_two
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) (k : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      badOneTermCount x ≤ 4 ^ k * badOneTermCount (x / 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hhalf := eventually_badOneTermCount_le_four_mul_half hlimit
      have hdivTop : Tendsto (fun x : ℕ => x / 2) atTop atTop :=
        Nat.tendsto_div_const_atTop (by norm_num)
      have ihHalf := hdivTop.eventually ih
      filter_upwards [hhalf, ihHalf] with x hx hih
      calc
        badOneTermCount x ≤ 4 * badOneTermCount (x / 2) := hx
        _ ≤ 4 * (4 ^ k * badOneTermCount ((x / 2) / 2 ^ k)) :=
          Nat.mul_le_mul_left 4 hih
        _ = 4 ^ (k + 1) * badOneTermCount (x / 2 ^ (k + 1)) := by
          simp only [Nat.div_div_eq_div_mul, pow_succ]
          ac_rfl

/-- Multiplication by a fixed positive power of two tends to infinity on
natural endpoints. -/
theorem tendsto_pow_two_mul_nat_atTop (k : ℕ) :
    Tendsto (fun x : ℕ => 2 ^ k * x) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun x hx => ?_⟩
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact hx.trans (le_mul_of_one_le_left' hpow)

/-- Every fixed positive floored dilation is bounded above by multiplication
by some power of two. -/
theorem exists_taoNaturalDilation_le_pow_two_mul
    {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ∀ x : ℕ, taoNaturalDilation c x ≤ 2 ^ k * x := by
  obtain ⟨k, hk⟩ := exists_nat_gt c
  refine ⟨k, fun x => ?_⟩
  have hmulPow : 2 * k ≤ 2 ^ k := Nat.mul_le_pow (by decide) k
  have hkPowNat : k ≤ 2 ^ k := by omega
  have hcPow : c ≤ (2 ^ k : ℕ) := hk.le.trans (by exact_mod_cast hkPowNat)
  have hfloor : (taoNaturalDilation c x : ℝ) ≤ c * x := by
    exact Nat.floor_le (mul_nonneg hc.le (Nat.cast_nonneg x))
  have hmul : c * (x : ℝ) ≤ ((2 ^ k * x : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hcPow (Nat.cast_nonneg x)
  exact_mod_cast hfloor.trans hmul

/-- Every fixed positive floored dilation is bounded below by division by
some power of two.  This is the exact floor-rounding bridge needed for a
contraction multiplier. -/
theorem exists_div_pow_two_le_taoNaturalDilation
    {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ∀ x : ℕ, x / 2 ^ k ≤ taoNaturalDilation c x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / c)
  refine ⟨k, fun x => ?_⟩
  have hmulPow : 2 * k ≤ 2 ^ k := Nat.mul_le_pow (by decide) k
  have hkPowNat : k ≤ 2 ^ k := by omega
  have hInvPow : (1 / c : ℝ) ≤ (2 ^ k : ℕ) :=
    hk.le.trans (by exact_mod_cast hkPowNat)
  have hPowPos : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have hInvLe : (1 / ((2 ^ k : ℕ) : ℝ)) ≤ c := by
    have hone : (1 : ℝ) ≤ (2 ^ k : ℕ) * c :=
      (div_le_iff₀ hc).mp hInvPow
    exact (div_le_iff₀ hPowPos).2 (by simpa [mul_comm] using hone)
  rw [taoNaturalDilation,
    Nat.le_floor_iff (mul_nonneg hc.le (Nat.cast_nonneg x))]
  calc
    ((x / 2 ^ k : ℕ) : ℝ) ≤ (x : ℝ) / (2 ^ k : ℕ) := Nat.cast_div_le
    _ = (1 / ((2 ^ k : ℕ) : ℝ)) * (x : ℝ) := by ring
    _ ≤ c * (x : ℝ) :=
      mul_le_mul_of_nonneg_right hInvLe (Nat.cast_nonneg x)

/-- The sharp critical smooth-number dilation formula implies the complete
fixed-dilation comparability statement of Tao's Lemma 1.6(ii). -/
theorem taoLemma16ii_of_criticalSmoothDilationLimit
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    TaoLemma16iiConclusion := by
  intro c hc
  obtain ⟨kup, hkUp⟩ := exists_taoNaturalDilation_le_pow_two_mul hc
  obtain ⟨kdown, hkDown⟩ := exists_div_pow_two_le_taoNaturalDilation hc
  constructor
  · refine IsBigO.of_bound (4 ^ kup) ?_
    have hiter :=
      eventually_badOneTermCount_le_four_pow_mul_div_pow_two hlimit kup
    have hscale := tendsto_pow_two_mul_nat_atTop kup
    have hiterScale := hscale.eventually hiter
    filter_upwards [hiterScale] with x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hmono : badOneTermCount (taoNaturalDilation c x) ≤
        badOneTermCount (2 ^ kup * x) :=
      countUpTo_mono_right (hkUp x)
    have hquot : (2 ^ kup * x) / 2 ^ kup = x := by
      exact Nat.mul_div_cancel_left x (by positivity : 0 < 2 ^ kup)
    have hnat : badOneTermCount (taoNaturalDilation c x) ≤
        4 ^ kup * badOneTermCount x := by
      exact hmono.trans (by simpa [hquot] using hx)
    exact_mod_cast hnat
  · refine IsBigO.of_bound (4 ^ kdown) ?_
    have hiter :=
      eventually_badOneTermCount_le_four_pow_mul_div_pow_two hlimit kdown
    filter_upwards [hiter] with x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hmono : badOneTermCount (x / 2 ^ kdown) ≤
        badOneTermCount (taoNaturalDilation c x) :=
      countUpTo_mono_right (hkDown x)
    have hnat : badOneTermCount x ≤
        4 ^ kdown * badOneTermCount (taoNaturalDilation c x) :=
      hx.trans (Nat.mul_le_mul_left _ hmono)
    exact_mod_cast hnat

/-- The sharp critical smooth-number dilation formula supplies exactly the
adjacent dyadic ratio used by the final summation. -/
theorem badOneTermDyadicRatio_of_criticalSmoothDilationLimit
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    TaoBadOneTermDyadicRatioConclusion := by
  have hhalf := tendsto_badOneTermCount_half_div_self hlimit
  have hpow : Tendsto (fun r : ℕ => 2 ^ (r + 1)) atTop atTop := by
    have hbase : Tendsto (fun r : ℕ => 2 ^ r) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hsucc : Tendsto (fun r : ℕ => r + 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun r hr => hr.trans (Nat.le_add_right r 1)⟩
    exact hbase.comp hsucc
  have hdyadic := hhalf.comp hpow
  simpa [TaoBadOneTermDyadicRatioConclusion, Function.comp_def,
    pow_succ] using hdyadic

/-- The sharp critical smooth-number dilation formula discharges the
regular-variation input in the conditional Theorem 1.7 endpoint. -/
theorem taoTheorem17_of_criticalSmoothDilationLimit
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    TaoTheorem17Conclusion :=
  taoTheorem17_of_badOneTermDyadicRatio hC hburgess hSS
    (taoLemma16ii_of_criticalSmoothDilationLimit hlimit)
    (badOneTermDyadicRatio_of_criticalSmoothDilationLimit hlimit)

/-- Explicit Burgess together with the sharp critical smooth-number dilation
formula proves Theorem 1.7 without an unrestricted Sylvester--Schur
hypothesis. -/
theorem taoTheorem17_of_criticalSmoothDilationLimit_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hlimit : TaoCriticalSmoothDilationLimitConclusion) :
    TaoTheorem17Conclusion :=
  taoTheorem17_of_explicitBurgess hC hburgess
    (taoLemma16ii_of_criticalSmoothDilationLimit hlimit)
    (badOneTermDyadicRatio_of_criticalSmoothDilationLimit hlimit)

/-- The single Gaussian saddle asymptotic target is therefore also a
source-faithful sufficient analytic input for the conditional Theorem 1.7
endpoint. -/
theorem taoTheorem17_of_criticalSmoothSaddleAsymptotic
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (hasymptotic : TaoCriticalSmoothSaddleAsymptoticConclusion) :
    TaoTheorem17Conclusion :=
  taoTheorem17_of_criticalSmoothDilationLimit hC hburgess hSS
    (criticalSmoothDilationLimit_of_saddleAsymptotic hasymptotic)

/-- The source-faithful Gaussian saddle asymptotic and explicit Burgess are
the two remaining analytic inputs for Theorem 1.7. -/
theorem taoTheorem17_of_criticalSmoothSaddleAsymptotic_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hasymptotic : TaoCriticalSmoothSaddleAsymptoticConclusion) :
    TaoTheorem17Conclusion :=
  taoTheorem17_of_criticalSmoothDilationLimit_explicitBurgess hC hburgess
    (criticalSmoothDilationLimit_of_saddleAsymptotic hasymptotic)

/-- Under the sharp critical smooth-number dilation formula, doubling the
cofactor cutoff doubles the entire slowly diagonalized central packet. -/
theorem tendsto_taoSlowCentralOneTermDoubledMass_div
    (hlimit : TaoCriticalSmoothDilationLimitConclusion)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hne : ∀ᶠ x : ℕ in atTop,
      (taoSlowCentralOneTermPrimeRange (q x) x).Nonempty) :
    Tendsto (fun x =>
      taoSlowCentralOneTermDoubledMass (q x) x /
        taoSlowCentralOneTermMass (q x) x) atTop (𝓝 (2 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huniform : ∀ᶠ x : ℕ in atTop,
      ∀ p, p ∈ taoSlowCentralOneTermPrimeRange (q x) x →
        2 - ε <
            (psiNat (2 * (x / p ^ 2)) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) ∧
          (psiNat (2 * (x / p ^ 2)) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) < 2 + ε := by
    apply eventually_forall_of_forall_selector
      (R := fun x p => p ∈ taoSlowCentralOneTermPrimeRange (q x) x)
      (P := fun x p =>
        2 - ε <
            (psiNat (2 * (x / p ^ 2)) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) ∧
          (psiNat (2 * (x / p ^ 2)) p : ℝ) /
              (psiNat (x / p ^ 2) p : ℝ) < 2 + ε)
    · filter_upwards [hne] with x hx
      exact hx
    · intro P hP
      have hregime :=
        isTaoCriticalSmoothRegime_natDiv_sq_of_mem_taoSlowCentral hq hP
      have hratio := hlimit 2 1 (fun x => x / P x ^ 2) P
        (by norm_num) (by norm_num) hregime
      have hnear := hratio.eventually
        (Ioo_mem_nhds (show 2 - ε < (2 : ℝ) by linarith)
          (show (2 : ℝ) < 2 + ε by linarith))
      simpa only [taoNaturalDilation_two] using hnear
  rw [eventually_atTop] at hne huniform
  obtain ⟨N₁, hN₁⟩ := hne
  obtain ⟨N₂, hN₂⟩ := huniform
  refine ⟨max N₁ N₂, fun x hx => ?_⟩
  have hnonempty := hN₁ x ((Nat.le_max_left _ _).trans hx)
  have hbounds := hN₂ x ((Nat.le_max_right _ _).trans hx)
  have hdenPos : 0 < taoSlowCentralOneTermMass (q x) x :=
    taoSlowCentralOneTermMass_pos hnonempty
  have hlower : (2 - ε) * taoSlowCentralOneTermMass (q x) x <
      taoSlowCentralOneTermDoubledMass (q x) x := by
    unfold taoSlowCentralOneTermMass taoSlowCentralOneTermDoubledMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact hnonempty
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpData.1).1
      have hpSq : p ^ 2 ≤ x := by
        rw [pow_two]
        exact Nat.le_sqrt.mp hpRange.2
      have hpsiPos : (0 : ℝ) < psiNat (x / p ^ 2) p := by
        exact_mod_cast one_le_psiNat
          (Nat.div_pos hpSq
            (pow_pos (Finset.mem_filter.mp hpData.1).2.pos 2))
      exact (lt_div_iff₀ hpsiPos).mp (hbounds p hp).1
  have hupper : taoSlowCentralOneTermDoubledMass (q x) x <
      (2 + ε) * taoSlowCentralOneTermMass (q x) x := by
    unfold taoSlowCentralOneTermMass taoSlowCentralOneTermDoubledMass
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact hnonempty
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpData.1).1
      have hpSq : p ^ 2 ≤ x := by
        rw [pow_two]
        exact Nat.le_sqrt.mp hpRange.2
      have hpsiPos : (0 : ℝ) < psiNat (x / p ^ 2) p := by
        exact_mod_cast one_le_psiNat
          (Nat.div_pos hpSq
            (pow_pos (Finset.mem_filter.mp hpData.1).2.pos 2))
      exact (div_lt_iff₀ hpsiPos).mp (hbounds p hp).2
  rw [Real.dist_eq]
  rw [abs_lt]
  have hratioLower : 2 - ε <
      taoSlowCentralOneTermDoubledMass (q x) x /
        taoSlowCentralOneTermMass (q x) x :=
    (lt_div_iff₀ hdenPos).2 hlower
  have hratioUpper :
      taoSlowCentralOneTermDoubledMass (q x) x /
          taoSlowCentralOneTermMass (q x) x < 2 + ε :=
    (div_lt_iff₀ hdenPos).2 hupper
  constructor
  · linarith only [hratioLower]
  · linarith only [hratioUpper]

end

end Tao2026
