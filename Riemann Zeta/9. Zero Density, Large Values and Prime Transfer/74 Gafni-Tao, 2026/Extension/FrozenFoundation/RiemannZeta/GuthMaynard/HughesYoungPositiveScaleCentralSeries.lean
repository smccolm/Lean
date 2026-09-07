import RiemannZeta.GuthMaynard.HughesYoungCentralSeriesFubiniNegative

open Complex MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 800000

namespace RiemannZeta.GuthMaynard

/-!
# Central-series Tonelli bounds at every positive Hughes--Young scale

The initial dyadic box has scale `1 / sqrt 2`, so the equation-(27) series
must be controlled for positive scales below one even though DFI equation (2)
itself is invoked only on the ordinary boxes.  The spare constant in the
logarithmic profile is replaced here by the exact scale dependence
`|log X| + log 2`.  This gives the same inverse-square/log-squared summable
majorant without falsely manufacturing an equation-(2) structure.
-/

/-- A series with measurable terms and finite summed `L¹` enorm is
integrable.  This is the exact companion to `integral_tsum` needed below;
it records integrability of the reassembled source rather than relying on
the totalized value of a nonintegrable Bochner integral. -/
theorem integrable_tsum_of_tsum_lintegral_enorm_ne_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℂ}
    (hMeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hFinite : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ ≠ ∞) :
    Integrable (fun x => ∑' n, F n x) μ := by
  have hNormMeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) μ :=
    (hMeas n).enorm
  have hPointwise : ∀ᵐ x ∂μ, Summable (fun n => (‖F n x‖₊ : ℝ)) := by
    rw [← lintegral_tsum hNormMeas] at hFinite
    refine (ae_lt_top' (AEMeasurable.tsum hNormMeas) hFinite).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hBoundInt : Integrable (fun x => ∑' n, ‖F n x‖) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hMeas n).norm), ?_⟩
    dsimp [HasFiniteIntegral]
    have hTop : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ < ∞ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hFinite
    convert hTop using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm,
      NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  refine hBoundInt.mono' (AEStronglyMeasurable.tsum hMeas) ?_
  filter_upwards [hPointwise] with x hx
  exact norm_tsum_le_tsum_norm hx

/-- The logarithm on a positive dyadic interval is bounded uniformly at an
arbitrary positive scale. -/
theorem abs_log_le_abs_log_scale_add_log_two_of_mem_Icc
    {S x : ℝ} (hS : 0 < S) (hx : x ∈ Set.Icc S (2 * S)) :
    |Real.log x| ≤ |Real.log S| + Real.log 2 := by
  have hx0 : 0 < x := hS.trans_le hx.1
  let z : ℝ := x / S
  have hz0 : 0 < z := div_pos hx0 hS
  have hz1 : 1 ≤ z := (le_div_iff₀ hS).2 (by simpa using hx.1)
  have hz2 : z ≤ 2 := (div_le_iff₀ hS).2 (by simpa only [two_mul] using hx.2)
  have hxmul : x = S * z := by
    dsimp only [z]
    field_simp
  rw [hxmul, Real.log_mul hS.ne' hz0.ne']
  calc
    |Real.log S + Real.log z| ≤ |Real.log S| + |Real.log z| := abs_add_le _ _
    _ = |Real.log S| + Real.log z := by
      rw [abs_of_nonneg (Real.log_nonneg hz1)]
    _ ≤ |Real.log S| + Real.log 2 :=
      add_le_add_right (Real.log_le_log hz0 hz2) _

/-- The positive-scale replacement for the equation-(27) modulus profile. -/
noncomputable def hughesYoungPositiveScaleCentralModulusProfile
    (X Y : ℝ) (a b q : ℕ) : ℝ :=
  let A := 1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant|
  ((q : ℝ) ^ 2)⁻¹ * (A + 2 * Real.log (q : ℝ)) ^ 2

theorem summable_hughesYoungPositiveScaleCentralModulusProfile
    (X Y : ℝ) (a b : ℕ) :
    Summable (hughesYoungPositiveScaleCentralModulusProfile X Y a b) := by
  let A := 1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant|
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  simpa only [hughesYoungPositiveScaleCentralModulusProfile, A] using
    summable_natCast_inv_sq_mul_log_profile_sq A hA

theorem hughesYoungPositiveScaleCentralModulusProfile_nonneg
    (X Y : ℝ) (a b q : ℕ) :
    0 ≤ hughesYoungPositiveScaleCentralModulusProfile X Y a b q := by
  unfold hughesYoungPositiveScaleCentralModulusProfile
  positivity

/-- A logarithmic factor in equation (27), uniformly on an arbitrary
positive dyadic box. -/
theorem norm_dfiEquation27LogFactor_reduced_le_positiveScaleProfile
    {S R : ℝ} (hS : 0 < S)
    (a b q : ℕ) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Icc S (2 * S)) :
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
      1 + |Real.log S| + Real.log 2 + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log R| + Real.log 2 +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
  have hxlog := abs_log_le_abs_log_scale_add_log_two_of_mem_Icc hS hx
  have hred := abs_log_dfiReducedDenominator_le a q hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbase := norm_dfiEquation27LogFactor_le
    a (dfiReducedDenominator a q) x
  calc
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
        |Real.log x| + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator a q : ℝ)| := hbase
    _ ≤ 1 + |Real.log S| + Real.log 2 + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log R| + Real.log 2 +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
      linarith [abs_nonneg (Real.log R), abs_nonneg (Real.log (b : ℝ)),
        abs_nonneg Real.eulerMascheroniConstant]

/-- Uniform positive-scale physical-kernel bound, with all modulus
dependence exposed in a summable profile. -/
theorem norm_hughesYoungCentralHeightKernel_le_positiveScale
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t x : ℝ) :
      ‖hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        (1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
          |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
          2 * Real.log (q : ℝ)) ^ 2 * B := by
  by_cases hz : hughesYoungCentralHeightBase
      T t c u X Y h k (r : ℤ) x = 0
  · rw [show hughesYoungCentralHeightKernel
        T t c u X Y h k a b r q x = 0 by
          simp [hughesYoungCentralHeightKernel, hz]]
    simpa only [norm_zero] using mul_nonneg (sq_nonneg
      (1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ))) hB
  · have hs := hughesYoungCentralHeightBase_mem_support_box
      hT c u hX hY h k (r : ℤ) hz
    let P : ℝ := 1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
      |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)
    have hP : 0 ≤ P := by
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
      have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      dsimp only [P]
      positivity
    have hleft :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤ P := by
      simpa only [P] using
        norm_dfiEquation27LogFactor_reduced_le_positiveScaleProfile
          (R := Y) hX a b q hq hs.2.1
    have hright :
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q)
          (x - (r : ℝ))‖ ≤ P := by
      have hswap := norm_dfiEquation27LogFactor_reduced_le_positiveScaleProfile
        (R := X) hY b a q hq hs.2.2
      dsimp only [P]
      calc
        _ ≤ 1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
            |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ) := hswap
        _ = _ := by ring
    unfold hughesYoungCentralHeightKernel
    simp only [norm_mul]
    calc
      _ ≤ P * P * B := by gcongr; exact hbaseBound t x
      _ = P ^ 2 * B := by ring

/-- Integration over the positive dyadic support preserves the generalized
summable profile. -/
theorem norm_integral_hughesYoungCentralHeightKernel_le_positiveScale
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t : ℝ) :
      ‖∫ x : ℝ,
          hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        X * ((1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
          |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
          2 * Real.log (q : ℝ)) ^ 2 * B) := by
  have hbound := norm_hughesYoungCentralHeightKernel_le_positiveScale
    hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
      hq hB hbaseBound
  have heq : (∫ x : ℝ,
      hughesYoungCentralHeightKernel T t c u X Y h k a b r q x) =
      ∫ x in Set.Icc X (2 * X),
        hughesYoungCentralHeightKernel T t c u X Y h k a b r q x := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hX hn)
      unfold hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
    simp [hweight]
  rw [heq]
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc X (2 * X))
    (C := (1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
      |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)) ^ 2 * B)
    (f := hughesYoungCentralHeightKernel T t c u X Y h k a b r q)
    measure_Icc_lt_top (fun x _hx => hbound t x)
  rw [Real.volume_real_Icc_of_le (by linarith : X ≤ 2 * X)] at hset
  calc
    _ ≤ ((1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) * X := by
      convert hset using 1
      ring
    _ = _ := by ring

/-- Every positive-scale positive-shift height term is dominated by the
generalized summable profile. -/
theorem exists_uniform_norm_hughesYoungCentralSeriesHeightTerm_le_positiveScaleProfile
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, ∀ t : ℝ,
      ‖hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q‖ ≤
        D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q := by
  obtain ⟨B, hB, hbaseBound⟩ :=
    exists_uniform_norm_hughesYoungCentralHeightBase_le
      hT hc u hX hY hh hk (r : ℤ)
  let D : ℝ := ‖(((a : ℂ) * b)⁻¹)‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * X * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungPositiveScaleCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b r q ha hb hr
    have hIntegral :=
      norm_integral_hughesYoungCentralHeightKernel_le_positiveScale
        hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
          hq hB hbaseBound t
    rw [hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((a : ℂ) * b)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ‖∫ x : ℝ,
            hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (X * ((1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
            |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q := by
        dsimp only [D, hughesYoungPositiveScaleCentralModulusProfile]
        ring

theorem tsum_lintegral_enorm_hughesYoungCentralSeriesHeightTerm_positiveScale_ne_top
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∑' q : ℕ, ∫⁻ t : ℝ,
      ‖hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q‖ₑ ≠ ∞ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungCentralSeriesHeightTerm_le_positiveScaleProfile
      hT hc u hX hY hh hk ha hb hr
  apply tsum_lintegral_enorm_ne_top_of_summable_bound_Icc
    (g := fun q => D * hughesYoungPositiveScaleCentralModulusProfile X Y a b q)
  · intro q
    exact mul_nonneg hD
      (hughesYoungPositiveScaleCentralModulusProfile_nonneg X Y a b q)
  · exact (summable_hughesYoungPositiveScaleCentralModulusProfile X Y a b).mul_left D
  · intro q
    exact support_hughesYoungCentralSeriesHeightTerm_subset
      hT c u X Y h k a b r q
  · exact hbound

/-- Series-level Fubini for every positive Hughes--Young scale, including the
initial `1 / sqrt 2` box. -/
theorem dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
  exact dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral_of_tonelli
    hT hc u hX hY hh hk a b r
      (tsum_lintegral_enorm_hughesYoungCentralSeriesHeightTerm_positiveScale_ne_top
        hT hc u hX hY hh hk ha hb hr)

/-- At a fixed ordinate the height-weighted positive central modulus series
is absolutely summable at every positive pair of dyadic scales.  This is the
pointwise input needed to reassemble the initial Hughes--Young box together
with all ordinary boxes. -/
theorem summable_hughesYoungCentralSeriesHeightTerm_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (t : ℝ) :
    Summable (fun q : ℕ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) := by
  obtain ⟨D, _hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungCentralSeriesHeightTerm_le_positiveScaleProfile
      hT hc u hX hY hh hk ha hb hr
  apply Summable.of_norm_bounded
    ((summable_hughesYoungPositiveScaleCentralModulusProfile X Y a b).mul_left D)
  intro q
  exact hbound q t

/-- Away from a zero of the height cutoff, summability of the weighted
series implies summability of the literal positive DFI central series. -/
theorem summable_dfiEquation27CentralSummand_fullDyadic_of_heightWeight_ne
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) {t : ℝ}
    (ht : hughesYoungHeightWeight T t ≠ 0) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) q) := by
  have htC : (hughesYoungHeightWeight T t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hs :=
    (summable_hughesYoungCentralSeriesHeightTerm_positiveScale
      hT hc u hX hY hh hk ha hb hr t).mul_left
        ((hughesYoungHeightWeight T t : ℂ)⁻¹)
  simpa only [hughesYoungCentralSeriesHeightTerm, ← mul_assoc,
    inv_mul_cancel₀ htC, one_mul] using hs

/-- The complete positive central series under the height cutoff is an
honest integrable function at every positive dyadic scale. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries a b r
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q
  have hMeas : ∀ q, AEStronglyMeasurable (F q) := fun q =>
    (continuous_hughesYoungCentralSeriesHeightTerm
      T hc u hX hY hh hk a b r q).aestronglyMeasurable
  have hInt := integrable_tsum_of_tsum_lintegral_enorm_ne_top hMeas
    (tsum_lintegral_enorm_hughesYoungCentralSeriesHeightTerm_positiveScale_ne_top
      hT hc u hX hY hh hk ha hb hr)
  simpa only [F, hughesYoungCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hInt

/-! ## Negative-shift companion -/

theorem norm_hughesYoungNegativeCentralHeightKernel_le_positiveScale
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t x : ℝ) :
    ‖hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
      (1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B := by
  by_cases hz : hughesYoungNegativeCentralHeightBase
      T t c u X Y h k (r : ℤ) x = 0
  · rw [show hughesYoungNegativeCentralHeightKernel
        T t c u X Y h k a b r q x = 0 by
          simp [hughesYoungNegativeCentralHeightKernel, hz]]
    simpa only [norm_zero] using mul_nonneg (sq_nonneg
      (1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ))) hB
  · have hs := hughesYoungNegativeCentralHeightBase_mem_support_box
      hT c u hX hY h k (r : ℤ) hz
    let P : ℝ := 1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)
    have hP : 0 ≤ P := by
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
      have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      dsimp only [P]
      positivity
    have hleft :
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q) x‖ ≤ P := by
      simpa only [P] using
        norm_dfiEquation27LogFactor_reduced_le_positiveScaleProfile
          (R := X) hY b a q hq hs.2.2
    have hright :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q)
          (x - (r : ℝ))‖ ≤ P := by
      have hswap := norm_dfiEquation27LogFactor_reduced_le_positiveScaleProfile
        (R := Y) hX a b q hq hs.2.1
      dsimp only [P]
      calc
        _ ≤ 1 + |Real.log X| + Real.log 2 + |Real.log (a : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log Y| + Real.log 2 +
            |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ) := hswap
        _ = _ := by ring
    unfold hughesYoungNegativeCentralHeightKernel
    simp only [norm_mul]
    calc
      _ ≤ P * P * B := by gcongr; exact hbaseBound t x
      _ = P ^ 2 * B := by ring

theorem norm_integral_hughesYoungNegativeCentralHeightKernel_le_positiveScale
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t : ℝ) :
    ‖∫ x : ℝ,
        hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
      Y * ((1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) := by
  have hbound := norm_hughesYoungNegativeCentralHeightKernel_le_positiveScale
    hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
      hq hB hbaseBound
  have heq : (∫ x : ℝ,
      hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x) =
      ∫ x in Set.Icc Y (2 * Y),
        hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hY hn)
      unfold hughesYoungReducedLocalizedMellinWeight hughesYoungLocalizedLogKernel
      simp [hcut]
    unfold hughesYoungNegativeCentralHeightKernel
      hughesYoungNegativeCentralHeightBase
    simp [hweight]
  rw [heq]
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc Y (2 * Y))
    (C := (1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)) ^ 2 * B)
    (f := hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q)
    measure_Icc_lt_top (fun x _hx => hbound t x)
  rw [Real.volume_real_Icc_of_le (by linarith : Y ≤ 2 * Y)] at hset
  calc
    _ ≤ ((1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) * Y := by
      convert hset using 1
      ring
    _ = _ := by ring

theorem exists_uniform_norm_hughesYoungNegativeCentralSeriesHeightTerm_le_positiveScaleProfile
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, ∀ t : ℝ,
      ‖hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q‖ ≤
        D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q := by
  obtain ⟨B, hB, hbaseBound⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralHeightBase_le
      hT hc u hX hY hh hk (r : ℤ)
  let D : ℝ := ‖(((b : ℂ) * a)⁻¹)‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * Y * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungNegativeCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungPositiveScaleCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      b a r q hb ha hr
    have hIntegral :=
      norm_integral_hughesYoungNegativeCentralHeightKernel_le_positiveScale
        hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
          hq hB hbaseBound t
    rw [hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((b : ℂ) * a)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          ‖∫ x : ℝ,
            hughesYoungNegativeCentralHeightKernel
              T t c u X Y h k a b r q x‖ ≤
        ‖(((b : ℂ) * a)⁻¹)‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (Y * ((1 + |Real.log Y| + Real.log 2 + |Real.log (b : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + |Real.log X| + Real.log 2 +
            |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q := by
        dsimp only [D, hughesYoungPositiveScaleCentralModulusProfile]
        ring

theorem tsum_lintegral_enorm_hughesYoungNegativeCentralSeriesHeightTerm_positiveScale_ne_top
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∑' q : ℕ, ∫⁻ t : ℝ,
      ‖hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q‖ₑ ≠ ∞ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralSeriesHeightTerm_le_positiveScaleProfile
      hT hc u hX hY hh hk ha hb hr
  apply tsum_lintegral_enorm_ne_top_of_summable_bound_Icc
    (g := fun q => D * hughesYoungPositiveScaleCentralModulusProfile Y X b a q)
  · intro q
    exact mul_nonneg hD
      (hughesYoungPositiveScaleCentralModulusProfile_nonneg Y X b a q)
  · exact (summable_hughesYoungPositiveScaleCentralModulusProfile Y X b a).mul_left D
  · intro q
    exact support_hughesYoungNegativeCentralSeriesHeightTerm_subset
      hT c u X Y h k a b r q
  · exact hbound

theorem dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight
            T c u X Y h k (-(r : ℤ)))) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  exact dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral_of_tonelli
    hT hc u hX hY hh hk a b r
      (tsum_lintegral_enorm_hughesYoungNegativeCentralSeriesHeightTerm_positiveScale_ne_top
        hT hc u hX hY hh hk ha hb hr)

/-- Fixed-ordinate summability for the height-weighted negative-shift
central series at arbitrary positive dyadic scales. -/
theorem summable_hughesYoungNegativeCentralSeriesHeightTerm_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (t : ℝ) :
    Summable (fun q : ℕ =>
      hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q) := by
  obtain ⟨D, _hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralSeriesHeightTerm_le_positiveScaleProfile
      hT hc u hX hY hh hk ha hb hr
  apply Summable.of_norm_bounded
    ((summable_hughesYoungPositiveScaleCentralModulusProfile Y X b a).mul_left D)
  intro q
  exact hbound q t

/-- Away from a zero of the height cutoff, the literal coordinate-swapped
negative central series is summable at every positive scale. -/
theorem summable_dfiEquation27CentralSummand_swappedFullDyadic_of_heightWeight_ne
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) {t : ℝ}
    (ht : hughesYoungHeightWeight T t ≠ 0) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) q) := by
  have htC : (hughesYoungHeightWeight T t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hs :=
    (summable_hughesYoungNegativeCentralSeriesHeightTerm_positiveScale
      hT hc u hX hY hh hk ha hb hr t).mul_left
        ((hughesYoungHeightWeight T t : ℂ)⁻¹)
  simpa only [hughesYoungNegativeCentralSeriesHeightTerm, ← mul_assoc,
    inv_mul_cancel₀ htC, one_mul] using hs

/-- Integrability of the complete negative-shift central series under the
height cutoff at arbitrary positive scales. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedPositiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungNegativeCentralSeriesHeightTerm
      T t c u X Y h k a b r q
  have hMeas : ∀ q, AEStronglyMeasurable (F q) := fun q =>
    (continuous_hughesYoungNegativeCentralSeriesHeightTerm
      T hc u hX hY hh hk a b r q).aestronglyMeasurable
  have hInt := integrable_tsum_of_tsum_lintegral_enorm_ne_top hMeas
    (tsum_lintegral_enorm_hughesYoungNegativeCentralSeriesHeightTerm_positiveScale_ne_top
      hT hc u hX hY hh hk ha hb hr)
  simpa only [F, hughesYoungNegativeCentralSeriesHeightTerm,
    dfiEquation27CentralSeries, tsum_mul_left] using hInt

/-! ## Pointwise cancellation-preserving finite dyadic reassembly -/

/-- A finite family of positive-scale positive-shift central series may be
reassembled exactly under the actual height cutoff.  The cutoff-zero branch
is handled separately, so no false lower-scale DFI hypothesis is needed. -/
theorem heightWeight_mul_dfiEquation27CentralSeries_fullDyadic_finsetSum
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u t : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (s : Finset (ℕ × ℕ)) :
    (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries a b r
          (fun x y => ∑ ij ∈ s,
            hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2 x y) =
      ∑ ij ∈ s, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2) := by
  by_cases ht : hughesYoungHeightWeight T t = 0
  · simp [ht]
  · have hlin := dfiEquation27CentralSeries_finsetSum s
        (fun ij => hughesYoungFullDyadicReducedMellinWeight
          T t c u h k ij.1 ij.2) a b r
        (fun ij _hij =>
          summable_dfiEquation27CentralSummand_fullDyadic_of_heightWeight_ne
            hT hc u (hughesYoungFullDyadicScale_pos ij.1)
              (hughesYoungFullDyadicScale_pos ij.2)
              hh hk ha hb hr ht)
        (fun q ij _hij =>
          integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
            T t c u (hughesYoungFullDyadicScale_pos ij.1)
              (hughesYoungFullDyadicScale_pos ij.2) hh hk a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q) r)
    rw [hlin, Finset.mul_sum]

/-- Negative-shift companion to the preceding finite reassembly theorem. -/
theorem heightWeight_mul_dfiEquation27CentralSeries_swappedFullDyadic_finsetSum
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u t : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (s : Finset (ℕ × ℕ)) :
    (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight (fun x y => ∑ ij ∈ s,
            hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2 x y)) =
      ∑ ij ∈ s, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2)) := by
  by_cases ht : hughesYoungHeightWeight T t = 0
  · simp [ht]
  · have hswap :
        dfiSwapWeight (fun x y => ∑ ij ∈ s,
          hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2 x y) =
          fun x y => ∑ ij ∈ s, dfiSwapWeight
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2) x y := by
        funext x y
        simp only [dfiSwapWeight]
    rw [hswap]
    have hlin := dfiEquation27CentralSeries_finsetSum s
        (fun ij => dfiSwapWeight
          (hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2)) b a r
        (fun ij _hij =>
          summable_dfiEquation27CentralSummand_swappedFullDyadic_of_heightWeight_ne
            hT hc u (hughesYoungFullDyadicScale_pos ij.1)
              (hughesYoungFullDyadicScale_pos ij.2)
              hh hk ha hb hr ht)
        (fun q ij _hij => by
          have hi :=
            integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
              T t c u (hughesYoungFullDyadicScale_pos ij.1)
                (hughesYoungFullDyadicScale_pos ij.2) hh hk a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (-(r : ℝ))
          have hshift := hi.comp_add_right (-(r : ℝ))
          convert hshift using 1
          funext x
          unfold dfiEquation27C dfiSwapWeight
            hughesYoungFullDyadicReducedMellinWeight
          push_cast
          ring_nf)
    rw [hlin, Finset.mul_sum]

/-- The complete signed DFI central series commutes with a finite dyadic
sum under the actual height weight, including the initial scale. -/
theorem heightWeight_mul_dfiSignedCentralSeries_fullDyadic_finsetSum
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u t : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0)
    (s : Finset (ℕ × ℕ)) :
    (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (fun x y => ∑ ij ∈ s,
            hughesYoungFullDyadicReducedMellinWeight
              T t c u h k ij.1 ij.2 x y) =
      ∑ ij ∈ s, (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungFullDyadicReducedMellinWeight
            T t c u h k ij.1 ij.2) := by
  by_cases hr0 : 0 ≤ r
  · have hrNat : 0 < r.toNat := by
      have : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
      omega
    simp only [dfiSignedCentralSeries, if_pos hr0]
    exact heightWeight_mul_dfiEquation27CentralSeries_fullDyadic_finsetSum
      hT hc u t hh hk ha hb hrNat s
  · have hrNeg : r < 0 := lt_of_not_ge hr0
    have hrNat : 0 < (-r).toNat := by omega
    simp only [dfiSignedCentralSeries, if_neg hr0]
    exact
      heightWeight_mul_dfiEquation27CentralSeries_swappedFullDyadic_finsetSum
        hT hc u t hh hk ha hb hrNat s

/-- Integrability of one signed, nonzero-shift central source under the
height cutoff, uniformly covering the initial positive scale. -/
theorem integrable_heightWeight_mul_dfiSignedCentralSeries_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  by_cases hr0 : 0 ≤ r
  · have hrNat : 0 < r.toNat := by omega
    simp only [dfiSignedCentralSeries, if_pos hr0]
    exact integrable_heightWeight_mul_dfiEquation27CentralSeries_positiveScale
      hT hc u hX hY hh hk ha hb hrNat
  · have hrNat : 0 < (-r).toNat := by omega
    simp only [dfiSignedCentralSeries, if_neg hr0]
    exact
      integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedPositiveScale
        hT hc u hX hY hh hk ha hb hrNat

/-- Signed series-level Fubini on every positive dyadic scale. -/
theorem dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
  cases r with
  | ofNat r =>
      have hrPos : 0 < r := by
        by_contra hzero
        exact hr (congrArg Int.ofNat (Nat.eq_zero_of_not_pos hzero))
      exact dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral_positiveScale
        hT hc u hX hY hh hk ha hb hrPos
  | negSucc n =>
      let r : ℕ := n + 1
      have hrPos : 0 < r := by dsimp only [r]; omega
      have hrEq : Int.negSucc n = -((r : ℕ) : ℤ) := by
        dsimp only [r]
        omega
      rw [hrEq]
      simp_rw [dfiSignedCentralSeries_neg_ofNat a b r hrPos]
      exact
        dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral_positiveScale
          hT hc u hX hY hh hk ha hb hrPos

/-! ## Exact support at positive scales -/

theorem dfiLocalizedBox_eq_zero_on_large_positive_shift_of_pos
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 0 < Y) (hh : 2 * X < h) :
    ∀ x : ℝ, f x (x - h) = 0 := by
  intro x
  by_contra hne
  have hmem : (x, x - (h : ℝ)) ∈
      Function.support (Function.uncurry f) := hne
  have hs := hbox.support_subset hmem
  have hypos : 0 < x - (h : ℝ) := hY.trans_le hs.2.1
  have hxupper : x ≤ 2 * X := hs.1.2
  exact (not_lt_of_ge hxupper) (hh.trans (by linarith))

theorem dfiEquation27CentralIntegral_eq_zero_of_large_positive_shift_of_pos
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 0 < Y) (hh : 2 * X < h)
    (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral a b qx qy f h = 0 := by
  have hfzero :=
    dfiLocalizedBox_eq_zero_on_large_positive_shift_of_pos hbox h hY hh
  unfold dfiEquation27CentralIntegral
  simp_rw [dfiEquation27C, hfzero]
  simp

theorem dfiEquation27CentralSeries_eq_zero_of_large_positive_shift_of_pos
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 0 < Y) (hh : 2 * X < h)
    (a b : ℕ) :
    dfiEquation27CentralSeries a b h f = 0 := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand,
    dfiEquation27CentralIntegral_eq_zero_of_large_positive_shift_of_pos
      hbox h hY hh a b]
  simp

theorem dfiSignedCentralSeries_eq_zero_of_outside_support_of_pos
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (hX : 0 < X) (hY : 0 < Y) (a b : ℕ) {r : ℤ} (hr : r ≠ 0)
    (hout : (0 ≤ r → 2 * X < (r.natAbs : ℝ)) ∧
      (r < 0 → 2 * Y < (r.natAbs : ℝ))) :
    dfiSignedCentralSeries a b r f = 0 := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn
        apply hr
        simp [Nat.eq_zero_of_not_pos hn]
      change dfiSignedCentralSeries a b (n : ℤ) f = 0
      rw [dfiSignedCentralSeries_ofNat]
      apply dfiEquation27CentralSeries_eq_zero_of_large_positive_shift_of_pos
        hbox n hY
      simpa using hout.1 (by positivity : (0 : ℤ) ≤ (n : ℤ))
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hrEq : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hrEq, dfiSignedCentralSeries_neg_ofNat a b m hm]
      apply dfiEquation27CentralSeries_eq_zero_of_large_positive_shift_of_pos
        hbox.swap m hX
      have hneg : -(m : ℤ) < 0 := by omega
      simpa [m] using hout.2 hneg

theorem hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale
    {T c u X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    DFILocalizedBox
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) X Y := by
  refine ⟨?_⟩
  intro p hp
  have hcore :
      hughesYoungDFICore T c u X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r p.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    change hughesYoungReducedCleanedShiftWeight T c u X Y h k r p.1 p.2 = 0
    rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    simp [hz]
  exact support_uncurry_hughesYoungDFICore_subset hX hY
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r hcore

theorem dfiSignedCentralSeries_reducedCleaned_eq_zero_of_outside_support_of_pos
    {T c u X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (a b : ℕ) {r : ℤ} (hr : r ≠ 0)
    (hout : (0 ≤ r → 2 * X < (r.natAbs : ℝ)) ∧
      (r < 0 → 2 * Y < (r.natAbs : ℝ))) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) = 0 := by
  exact dfiSignedCentralSeries_eq_zero_of_outside_support_of_pos
    (hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale hX hY h k r)
    hX hY a b hr hout

end RiemannZeta.GuthMaynard
