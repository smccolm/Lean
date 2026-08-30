import RiemannZeta.GuthMaynard.HughesYoungCentralSourceBridge
import RiemannZeta.GuthMaynard.HughesYoungSignedCentralAssembly
import RiemannZeta.GuthMaynard.HughesYoungFarShift
import RiemannZeta.GuthMaynard.HughesYoungPointwiseDFIAssembly
import RiemannZeta.GuthMaynard.HughesYoungPositiveScaleCentralSeries

open Complex Finset MeasureTheory Set
open scoped BigOperators Interval
open Classical

noncomputable section

set_option maxHeartbeats 800000

namespace RiemannZeta.GuthMaynard

/-!
# Completing the finite Hughes--Young central shift family

The DFI theorem is inserted only on the finite near-shift family.  The
Hughes--Young source calculation, however, evaluates the complete positive
and negative central series.  This file supplies the exact support and
finite-complement identities needed to pass between those two objects.
-/

/-- The exact reduced cleaned weight retains the localized DFI box support.
The height transform and the original mollifier scalar do not enlarge it. -/
theorem hughesYoungReducedCleanedShiftWeight_localizedBox
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

/-- A signed DFI central series vanishes outside the corresponding positive
or negative coordinate support.  This is the signed form of the exact
support statement following DFI equation (2). -/
theorem dfiSignedCentralSeries_eq_zero_of_outside_support
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y) (a b : ℕ) {r : ℤ} (hr : r ≠ 0)
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
        hbox n (by linarith)
      simpa using hout.1 (by positivity : (0 : ℤ) ≤ (n : ℤ))
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hrEq : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hrEq, dfiSignedCentralSeries_neg_ofNat a b m hm]
      apply dfiEquation27CentralSeries_eq_zero_of_large_positive_shift_of_pos
        hbox.swap m (by linarith)
      have hneg : -(m : ℤ) < 0 := by omega
      simpa [m] using hout.2 hneg

/-- Specialization of the signed support cutoff to the literal
Hughes--Young reduced cleaned weight. -/
theorem dfiSignedCentralSeries_reducedCleaned_eq_zero_of_outside_support
    {T c u X Y : ℝ} (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y)
    (h k : ℕ) (a b : ℕ) {r : ℤ} (hr : r ≠ 0)
    (hout : (0 ≤ r → 2 * X < (r.natAbs : ℝ)) ∧
      (r < 0 → 2 * Y < (r.natAbs : ℝ))) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) = 0 := by
  exact dfiSignedCentralSeries_eq_zero_of_outside_support
    (hughesYoungReducedCleanedShiftWeight_localizedBox
      (by linarith) (by linarith) h k r)
    hX hY a b hr hout

/-- The complete signed central contribution on the literal finite divisor
box.  The zero shift is excluded because it is the separately treated
diagonal. -/
noncomputable def hughesYoungFiniteCompleteSignedCentralBox
    (T c u X Y : ℝ) (h k a b M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungShiftInterval a b M N,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)

/-- The complementary signed central family on exactly the same far-shift
set as Hughes--Young equation (65). -/
noncomputable def hughesYoungFarSignedCentralBox
    (T c u P X Y : ℝ) (h k a b M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
    dfiSignedCentralSeries a b r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)

/-- Exact finite near/far decomposition of the DFI central series.  This is
an identity before any norm or estimate is taken. -/
theorem hughesYoungFiniteCompleteSignedCentralBox_eq_near_add_far
    (T c u P X Y : ℝ) (h k a b M N : ℕ) :
    hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N =
      (∑ r ∈ hughesYoungNearShifts T P X Y a b M N,
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) +
      hughesYoungFarSignedCentralBox T c u P X Y h k a b M N := by
  unfold hughesYoungFiniteCompleteSignedCentralBox
    hughesYoungFarSignedCentralBox
  exact sum_shiftInterval_eq_near_add_far
    (fun r => dfiSignedCentralSeries a b r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
    T P X Y a b M N

/-- Solving the preceding exact identity for the finite near family exposes
the complete central term and the one omitted central tail. -/
theorem sum_near_dfiSignedCentralSeries_eq_complete_sub_far
    (T c u P X Y : ℝ) (h k a b M N : ℕ) :
    (∑ r ∈ hughesYoungNearShifts T P X Y a b M N,
      dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) =
      hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N -
        hughesYoungFarSignedCentralBox T c u P X Y h k a b M N := by
  rw [hughesYoungFiniteCompleteSignedCentralBox_eq_near_add_far]
  ring

/-- The complete nonzero-shift DFI central family on one finite divisor
rectangle, integrated in the compact Hughes--Young Mellin ordinate. -/
noncomputable def hughesYoungIntegratedFiniteCompleteSignedCentralBox
    (T c H X Y : ℝ) (h k a b M N : ℕ) : ℂ :=
  ∫ u in -H..H, (T : ℂ) *
    hughesYoungFiniteCompleteSignedCentralBox
      T c u X Y h k a b M N

/-- Exact integrated form of the near/complete/far identity.  This is the
Hughes--Young equation-(81) extension step before the equation-(65) tail is
estimated. -/
theorem hughesYoungIntegratedPointwiseSignedCentral_near_eq_complete_sub_far
    (T c H P X Y : ℝ) (h k M N : ℕ) :
    hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k
        (hughesYoungNearShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) =
      ∫ u in -H..H, (T : ℂ) *
        (hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N -
          hughesYoungFarSignedCentralBox T c u P X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) := by
  unfold hughesYoungIntegratedPointwiseSignedCentral
  apply intervalIntegral.integral_congr
  intro u _hu
  change (T : ℂ) *
      (∑ r ∈ hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) = _
  rw [sum_near_dfiSignedCentralSeries_eq_complete_sub_far
    T c u P X Y h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N]

/-- Source-specialized version of the integrated extension identity. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_complete_sub_far
    (T c H P X Y : ℝ) (h k M N : ℕ) :
    hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N =
      ∫ u in -H..H, (T : ℂ) *
        (hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N -
          hughesYoungFarSignedCentralBox T c u P X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) := by
  unfold hughesYoungNearPointwiseSignedCentralBox
  exact hughesYoungIntegratedPointwiseSignedCentral_near_eq_complete_sub_far
    T c H P X Y h k M N

/-! ## Measurability and exact integral splitting

The far family lies outside the parameter range where the existing uniform
Weierstrass continuity theorem applies.  Continuity of each fixed modulus is
still enough: countable sums of strongly measurable functions are strongly
measurable.  This is the correct input for combining equation (65)'s
pointwise majorant with Bochner integrability. -/

/-- The signed equation-(27) series is strongly measurable in the Mellin
ordinate for every fixed nonzero shift.  This statement deliberately has no
near-shift restriction. -/
theorem aestronglyMeasurable_dfiSignedCentralSeries_reducedCleaned_ordinate
    {T c X Y : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    AEStronglyMeasurable (fun u : ℝ =>
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) := by
  cases r with
  | ofNat n =>
      have hmeas : AEStronglyMeasurable (fun u : ℝ => ∑' q : ℕ,
          dfiEquation27CentralSummand
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) n
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k (n : ℤ)) q) :=
        AEStronglyMeasurable.tsum fun q =>
        (continuous_dfiEquation27CentralSummand_reducedCleaned_ordinate
          hT hc hX hY hh hk n q).aestronglyMeasurable
      simpa only [dfiSignedCentralSeries_ofNat,
        dfiEquation27CentralSeries] using hmeas
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hr : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hr]
      rw [show (fun u : ℝ =>
          dfiSignedCentralSeries
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) (-(m : ℤ))
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(m : ℤ)))) =
        fun u : ℝ => ∑' q : ℕ,
          dfiEquation27CentralSummand
            (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) m
            (dfiSwapWeight
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(m : ℤ)))) q by
        funext u
        rw [dfiSignedCentralSeries_neg_ofNat
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) m hm]
        rfl]
      exact AEStronglyMeasurable.tsum fun q =>
        (continuous_dfiEquation27CentralSummand_swappedReducedCleaned_ordinate
          hT hc hX hY hh hk m q).aestronglyMeasurable

/-- The finite far-shift central family is strongly measurable without a
near-shift smoothness hypothesis. -/
theorem aestronglyMeasurable_hughesYoungFarSignedCentralBox
    {T c P X Y : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (M N : ℕ) :
    AEStronglyMeasurable (fun u : ℝ =>
      hughesYoungFarSignedCentralBox T c u P X Y h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) := by
  unfold hughesYoungFarSignedCentralBox
  let s := hughesYoungFarShifts T P X Y
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N
  let f : ℤ → ℝ → ℂ := fun r u =>
    dfiSignedCentralSeries
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
  have hmeas : AEStronglyMeasurable (∑ r ∈ s, f r) :=
    Finset.aestronglyMeasurable_sum s fun r _ =>
      aestronglyMeasurable_dfiSignedCentralSeries_reducedCleaned_ordinate
        hT hc hX hY hh hk r
  have heq : (fun u : ℝ => ∑ r ∈ s, f r u) = ∑ r ∈ s, f r := by
    funext u
    exact (Finset.sum_apply u s f).symm
  rw [heq]
  exact hmeas

/-! ## Equation-(65) decay for the omitted DFI central family -/

/-- The common logarithmic profile in the two factors of DFI equation (27).
It is nonnegative on every source dyadic box and positive modulus. -/
noncomputable def hughesYoungCentralLogProfile
    (X Y : ℝ) (a b q : ℕ) : ℝ :=
  1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
    2 * Real.log (q : ℝ)

theorem hughesYoungCentralLogProfile_nonneg
    {X Y : ℝ} (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y)
    (a b q : ℕ) (hq : 0 < q) :
    0 ≤ hughesYoungCentralLogProfile X Y a b q := by
  have hlogX : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  unfold hughesYoungCentralLogProfile
  positivity

/-- The equation-(27) logarithmic factor obeys the original central
profile down to the genuine lower dyadic scale.  The spare leading `1`
absorbs the possible negative logarithm on `[1/2,1]`. -/
theorem norm_dfiEquation27LogFactor_reduced_le_centralProfile_of_half
    {S R : ℝ} (hS : 1 / 2 ≤ S) (hR : 1 / 2 ≤ R)
    (a b q : ℕ) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Icc S (2 * S)) :
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
      1 + Real.log (2 * S) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * R) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
  have hS0 : 0 < S := by linarith
  have hx0 : 0 < x := hS0.trans_le hx.1
  have hlogS : 0 ≤ Real.log (2 * S) :=
    Real.log_nonneg (by linarith)
  have hlogR : 0 ≤ Real.log (2 * R) :=
    Real.log_nonneg (by linarith)
  have hxlog : |Real.log x| ≤ 1 + Real.log (2 * S) := by
    by_cases hx1 : 1 ≤ x
    · rw [abs_of_nonneg (Real.log_nonneg hx1)]
      have hlog := Real.log_le_log hx0 hx.2
      linarith
    · have hxlt : x < 1 := lt_of_not_ge hx1
      rw [abs_of_nonpos (Real.log_nonpos hx0.le hxlt.le)]
      have hlogLower := Real.log_le_log hS0 hx.1
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
          Real.log_one]
        ring
      have hhalfLog : -Real.log S ≤ Real.log 2 := by
        have hslog := Real.log_le_log (by norm_num : 0 < (1 / 2 : ℝ)) hS
        rw [hlogHalf] at hslog
        linarith
      have hTwo : Real.log 2 ≤ 1 :=
        Real.log_two_lt_d9.le.trans (by norm_num)
      linarith
  have hred := abs_log_dfiReducedDenominator_le a q hq
  have hbase := norm_dfiEquation27LogFactor_le
    a (dfiReducedDenominator a q) x
  calc
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
        |Real.log x| + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator a q : ℝ)| := hbase
    _ ≤ 1 + Real.log (2 * S) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * R) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
      linarith [abs_nonneg (Real.log (b : ℝ)),
        abs_nonneg Real.eulerMascheroniConstant]

/-- Equation (65) controls the complete logarithmic kernel occurring in one
positive-shift DFI central integral.  No derivative hypothesis from DFI is
used here: the integration by parts has already been carried out in the
physical height variable. -/
theorem exists_farShift_norm_dfiEquation27C_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ} {x : ℝ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < a → 0 < b → 0 < r → 0 < q →
      (r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ)) x (x - (r : ℝ))‖ ≤
        hughesYoungCentralLogProfile X Y a b q ^ 2 *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k x (x - (r : ℝ))‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ :=
    exists_farShift_reducedCleaned_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q x hT hc hc1 hu hP hPT
    hX hY ha hb hr hq hfar
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65nonneg : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  by_cases hw : hughesYoungReducedCleanedShiftWeight
      T c u X Y h k (r : ℤ) x (x - (r : ℝ)) = 0
  · simp only [dfiEquation27C, hw, mul_zero, norm_zero, mul_zero]
    positivity
  · have hstatic : hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k x (x - (r : ℝ)) ≠ 0 := by
      intro hz
      apply hw
      unfold hughesYoungReducedCleanedShiftWeight
      rw [hz]
      norm_num
    have hmem := hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
      hX0 hY0 hstatic
    have hx : 0 < x := hX0.trans_le hmem.1.1
    have hy : 0 < x - (r : ℝ) := hY0.trans_le hmem.2.1
    have hraw := h65 j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := (r : ℤ)) (x := x)
      (y := x - (r : ℝ)) hT hc hc1 hu hP hPT hX0 hY0 hx hy
      (by push_cast; ring) hfar
    have hleft := norm_dfiEquation27LogFactor_reduced_le_centralProfile_of_half
      hX hY a b q hq hmem.1
    have hleft' :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
          hughesYoungCentralLogProfile X Y a b q := by
      simpa only [hughesYoungCentralLogProfile] using hleft
    have hrightRaw := norm_dfiEquation27LogFactor_reduced_le_centralProfile_of_half
      hY hX b a q hq hmem.2
    have hright :
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q)
          (x - (r : ℝ))‖ ≤ hughesYoungCentralLogProfile X Y a b q := by
      calc
        _ ≤ 1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
              2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
              |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
              2 * Real.log (q : ℝ) := hrightRaw
        _ = hughesYoungCentralLogProfile X Y a b q := by
          unfold hughesYoungCentralLogProfile
          ring
    have hprofile := hughesYoungCentralLogProfile_nonneg hX hY a b q hq
    unfold dfiEquation27C
    simp only [norm_mul]
    calc
      (P / (5 * T)) ^ j *
          (‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ *
            ‖dfiEquation27LogFactor b (dfiReducedDenominator b q)
              (x - (r : ℝ))‖ *
            ‖hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ) x (x - (r : ℝ))‖) =
        (‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ *
          ‖dfiEquation27LogFactor b (dfiReducedDenominator b q)
            (x - (r : ℝ))‖) *
          ((P / (5 * T)) ^ j *
            ‖hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ) x (x - (r : ℝ))‖) := by ring
      _ ≤ (hughesYoungCentralLogProfile X Y a b q *
            hughesYoungCentralLogProfile X Y a b q) *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k x (x - (r : ℝ))‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        gcongr
      _ = _ := by ring

/-- The physical-scale factor left after equation (65) removes the height
oscillation from a reduced Hughes--Young box. -/
noncomputable def hughesYoungReducedStaticScale
    (T c X Y : ℝ) (h k : ℕ) : ℝ :=
  ‖hughesYoungLocalizedStaticScalar T h k‖ *
    (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
      ((1 / 2 : ℝ) + c) *
    (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
      ((1 / 2 : ℝ) + c)

theorem hughesYoungReducedStaticScale_nonneg
    (T c : ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h k : ℕ) :
    0 ≤ hughesYoungReducedStaticScale T c X Y h k := by
  unfold hughesYoungReducedStaticScale
  have hleft : 0 ≤ ((hughesYoungReducedLeft h k : ℕ) : ℝ) / X :=
    div_nonneg (by positivity) hX
  have hright : 0 ≤ ((hughesYoungReducedRight h k : ℕ) : ℝ) / Y :=
    div_nonneg (by positivity) hY
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hleft _))
    (Real.rpow_nonneg hright _)

/-- Integrated equation-(65) bound for one positive-shift DFI central
integral.  The interval length is exactly the source dyadic length `X`. -/
theorem exists_farShift_norm_dfiEquation27CentralIntegral_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r → 0 < q →
      (r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ)) r‖ ≤
        X * hughesYoungCentralLogProfile X Y a b q ^ 2 *
          ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hpoint⟩ :=
    exists_farShift_norm_dfiEquation27C_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hq hfar
  let F : ℝ → ℂ := fun x =>
    dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))
      x (x - (r : ℝ))
  let A : ℝ := (P / (5 * T)) ^ j
  let B : ℝ := hughesYoungCentralLogProfile X Y a b q ^ 2 *
    ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
      hughesYoungEquation65Bound Cγ Cw j T c u)
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65nonneg : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
          (mul_nonneg (by positivity)
          (hughesYoungReducedStaticScale_nonneg T c hX0.le hY0.le h k))
        h65nonneg)
  have hscalePoint : ∀ x : ℝ,
      ‖hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k x (x - (r : ℝ))‖ ≤
          hughesYoungReducedStaticScale T c X Y h k := by
    intro x
    by_cases hs : hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k x (x - (r : ℝ)) = 0
    · simp [hs, hughesYoungReducedStaticScale_nonneg T c hX0.le hY0.le]
    · have hmem := hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
        hX0 hY0 hs
      exact norm_hughesYoungReducedLocalizedStaticWeight_le_scale
        hX0 hY0 hmem.1.1 hmem.2.1 hh hk hc
  have hweighted : ∀ x : ℝ, ‖(A : ℂ) * F x‖ ≤ B := by
    intro x
    have hp := hpoint j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := r) (q := q) (x := x)
      hT hc hc1 hu hP hPT hX hY ha hb hr hq hfar
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    change A * ‖F x‖ ≤ B
    calc
      A * ‖F x‖ ≤ hughesYoungCentralLogProfile X Y a b q ^ 2 *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k x (x - (r : ℝ))‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        simpa only [A, F] using hp
      _ ≤ hughesYoungCentralLogProfile X Y a b q ^ 2 *
          ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hscalePoint x) (by positivity))
          h65nonneg
      _ = B := by rfl
  have hsupport : ∀ x ∉ Set.Icc X (2 * X), (A : ℂ) * F x = 0 := by
    intro x hx
    have hw : hughesYoungReducedCleanedShiftWeight
        T c u X Y h k (r : ℤ) x (x - (r : ℝ)) = 0 := by
      by_contra hn
      have hs : hughesYoungReducedLocalizedStaticWeight
          T c u X Y h k x (x - (r : ℝ)) ≠ 0 := by
        intro hz
        apply hn
        unfold hughesYoungReducedCleanedShiftWeight
        rw [hz]
        norm_num
      exact hx (hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
        hX0 hY0 hs).1
    simp [F, dfiEquation27C, hw]
  have hint : (∫ x : ℝ, (A : ℂ) * F x) =
      ∫ x in Set.Icc X (2 * X), (A : ℂ) * F x := by
    symm
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hsupport
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc X (2 * X)) (C := B)
    (f := fun x => (A : ℂ) * F x) measure_Icc_lt_top
    (fun x _hx => hweighted x)
  rw [Real.volume_real_Icc_of_le (by linarith : X ≤ 2 * X)] at hset
  have hnormIntegral :
      ‖∫ x : ℝ, (A : ℂ) * F x‖ ≤ B * X := by
    rw [hint]
    convert hset using 1
    ring
  rw [MeasureTheory.integral_const_mul, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg hA] at hnormIntegral
  have hfinal : A * ‖∫ x : ℝ, F x‖ ≤ X * B :=
    hnormIntegral.trans_eq (by ring)
  dsimp only [A, B, F] at hfinal
  unfold dfiEquation27CentralIntegral
  exact hfinal.trans_eq (by ring)

/-- The shift-dependent but modulus-independent factor in the positive
central-tail estimate. -/
noncomputable def hughesYoungFarCentralShiftScale
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    (T c u X Y : ℝ) (h k a b r : ℕ) : ℝ :=
  ‖(((a : ℂ) * b)⁻¹)‖ * ((a * b * r ^ 2 : ℕ) : ℝ) * X *
    ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
      hughesYoungEquation65Bound Cγ Cw j T c u)

theorem hughesYoungFarCentralShiftScale_nonneg
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    {T c u X Y : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hCw : ∀ i, 0 < Cw i) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h k a b r : ℕ) :
    0 ≤ hughesYoungFarCentralShiftScale Cγ Cw j T c u X Y h k a b r := by
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65 : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  unfold hughesYoungFarCentralShiftScale
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hX)
    (mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungReducedStaticScale_nonneg T c hX hY h k)) h65)

/-- One positive far-shift modulus summand has equation-(65) decay times
the exact inverse-square/log-squared summable profile. -/
theorem exists_farShift_norm_dfiEquation27CentralSummand_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r →
      (r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralSummand a b r
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ)) q‖ ≤
        hughesYoungFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            hughesYoungCentralModulusProfile X Y a b q := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hintegral⟩ :=
    exists_farShift_norm_dfiEquation27CentralIntegral_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hfar
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient,
      hughesYoungCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    have hInt := hintegral j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := r) (q := q)
      hT hc hc1 hu hP hPT hX hY hh hk ha hb hr hq hfar
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b r q ha hb hr
    have hfreq : 0 ≤ (P / (5 * T)) ^ j := by positivity
    unfold dfiEquation27CentralSummand
    simp only [norm_mul]
    calc
      (P / (5 * T)) ^ j *
          (‖(((a : ℂ) * b)⁻¹)‖ *
            ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
            ‖dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (hughesYoungReducedCleanedShiftWeight
                T c u X Y h k (r : ℤ)) r‖) =
        ‖(((a : ℂ) * b)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((P / (5 * T)) ^ j *
            ‖dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (hughesYoungReducedCleanedShiftWeight
                T c u X Y h k (r : ℤ)) r‖) := by ring
      _ ≤ ‖(((a : ℂ) * b)⁻¹)‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (X * hughesYoungCentralLogProfile X Y a b q ^ 2 *
            ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
              hughesYoungEquation65Bound Cγ Cw j T c u)) := by
        gcongr
      _ = hughesYoungFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            hughesYoungCentralModulusProfile X Y a b q := by
        unfold hughesYoungFarCentralShiftScale
          hughesYoungCentralModulusProfile hughesYoungCentralLogProfile
        ring

/-- The complete positive DFI central series on one omitted far shift has
arbitrary-order equation-(65) decay.  Absolute convergence is proved from
the displayed source profile rather than imported from a near-shift DFI
smoothness hypothesis. -/
theorem exists_farShift_norm_dfiEquation27CentralSeries_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r →
      (r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralSeries a b r
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (r : ℤ))‖ ≤
        hughesYoungFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hsummand⟩ :=
    exists_farShift_norm_dfiEquation27CentralSummand_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hfar
  let A : ℝ := (P / (5 * T)) ^ j
  let D : ℝ := hughesYoungFarCentralShiftScale Cγ Cw j
    T c u X Y h k a b r
  let f : ℕ → ℂ := fun q => dfiEquation27CentralSummand a b r
    (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) q
  let g : ℕ → ℝ := fun q => hughesYoungCentralModulusProfile X Y a b q
  have hT0 : 0 < T := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    exact pow_pos (div_pos hP (mul_pos (by norm_num) hT0)) j
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact hughesYoungFarCentralShiftScale_nonneg Cγ Cw j hT0 hc hCw
      (by linarith) (by linarith) h k a b r
  have hg : Summable g := by
    simpa only [g] using summable_hughesYoungCentralModulusProfile hX hY a b
  have hterm : ∀ q : ℕ, A * ‖f q‖ ≤ D * g q := by
    intro q
    simpa only [A, D, f, g] using
      hsummand j hT hc hc1 hu hP hPT hX hY hh hk ha hb hr hfar
  have hfNorm : Summable (fun q => ‖f q‖) := by
    have hmajor : Summable (fun q => A⁻¹ * (D * g q)) :=
      (hg.mul_left D).mul_left A⁻¹
    apply Summable.of_norm_bounded hmajor
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖f q‖ = A⁻¹ * (A * ‖f q‖) := by
        field_simp
      _ ≤ A⁻¹ * (D * g q) :=
        mul_le_mul_of_nonneg_left (hterm q) (by positivity)
  have hf : Summable f := Summable.of_norm hfNorm
  have hleft : A * ‖∑' q, f q‖ ≤ ∑' q, A * ‖f q‖ := by
    calc
      A * ‖∑' q, f q‖ ≤ A * ∑' q, ‖f q‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hfNorm) hA.le
      _ = ∑' q, A * ‖f q‖ := by rw [tsum_mul_left]
  have hright : (∑' q, A * ‖f q‖) ≤ ∑' q, D * g q := by
    exact Summable.tsum_le_tsum
      hterm (hfNorm.mul_left A) (hg.mul_left D)
  calc
    A * ‖∑' q, f q‖ ≤ ∑' q, A * ‖f q‖ := hleft
    _ ≤ ∑' q, D * g q := hright
    _ = D * ∑' q, g q := tsum_mul_left

/-! ## The negative signed central family -/

/-- Equation (65) for a negative source shift after the exact DFI coordinate
swap.  The far-range hypothesis deliberately remains in the original
`(X,Y,a,b,M,N)` coordinates; only the equation-(27) kernel is swapped. -/
theorem exists_negativeFarShift_norm_dfiEquation27C_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ} {y : ℝ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < a → 0 < b → 0 < r → 0 < q →
      -(r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27C b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)))) y (y - (r : ℝ))‖ ≤
        hughesYoungCentralLogProfile Y X b a q ^ 2 *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k (y - (r : ℝ)) y‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, h65⟩ :=
    exists_farShift_reducedCleaned_equation65
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q y hT hc hc1 hu hP hPT
    hX hY ha hb hr hq hfar
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65nonneg : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  by_cases hw : hughesYoungReducedCleanedShiftWeight
      T c u X Y h k (-(r : ℤ)) (y - (r : ℝ)) y = 0
  · simp only [dfiEquation27C, dfiSwapWeight, hw, mul_zero, norm_zero]
    positivity
  · have hstatic : hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k (y - (r : ℝ)) y ≠ 0 := by
      intro hz
      apply hw
      unfold hughesYoungReducedCleanedShiftWeight
      rw [hz]
      norm_num
    have hmem := hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
      hX0 hY0 hstatic
    have hx : 0 < y - (r : ℝ) := hX0.trans_le hmem.1.1
    have hy : 0 < y := hY0.trans_le hmem.2.1
    have hraw := h65 j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := -(r : ℤ)) (x := y - (r : ℝ))
      (y := y) hT hc hc1 hu hP hPT hX0 hY0 hx hy
      (by push_cast; ring) hfar
    have hleft := norm_dfiEquation27LogFactor_reduced_le_centralProfile_of_half
      hY hX b a q hq hmem.2
    have hleft' :
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q) y‖ ≤
          hughesYoungCentralLogProfile Y X b a q := by
      simpa only [hughesYoungCentralLogProfile] using hleft
    have hright := norm_dfiEquation27LogFactor_reduced_le_centralProfile_of_half
      hX hY a b q hq hmem.1
    have hright' :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q)
          (y - (r : ℝ))‖ ≤ hughesYoungCentralLogProfile Y X b a q := by
      calc
        _ ≤ 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
              2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
              |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
              2 * Real.log (q : ℝ) := hright
        _ = hughesYoungCentralLogProfile Y X b a q := by
          unfold hughesYoungCentralLogProfile
          ring
    have hprofile := hughesYoungCentralLogProfile_nonneg hY hX b a q hq
    unfold dfiEquation27C dfiSwapWeight
    simp only [norm_mul]
    calc
      (P / (5 * T)) ^ j *
          (‖dfiEquation27LogFactor b (dfiReducedDenominator b q) y‖ *
            ‖dfiEquation27LogFactor a (dfiReducedDenominator a q)
              (y - (r : ℝ))‖ *
            ‖hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)) (y - (r : ℝ)) y‖) =
        (‖dfiEquation27LogFactor b (dfiReducedDenominator b q) y‖ *
          ‖dfiEquation27LogFactor a (dfiReducedDenominator a q)
            (y - (r : ℝ))‖) *
          ((P / (5 * T)) ^ j *
            ‖hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)) (y - (r : ℝ)) y‖) := by ring
      _ ≤ (hughesYoungCentralLogProfile Y X b a q *
            hughesYoungCentralLogProfile Y X b a q) *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k (y - (r : ℝ)) y‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        gcongr
      _ = _ := by ring

/-- The physical factor for a negative signed central shift.  The integral
now runs in the second source variable and therefore has dyadic length `Y`. -/
noncomputable def hughesYoungNegativeFarCentralShiftScale
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    (T c u X Y : ℝ) (h k a b r : ℕ) : ℝ :=
  ‖(((b : ℂ) * a)⁻¹)‖ * ((b * a * r ^ 2 : ℕ) : ℝ) * Y *
    ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
      hughesYoungEquation65Bound Cγ Cw j T c u)

theorem hughesYoungNegativeFarCentralShiftScale_nonneg
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    {T c u X Y : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hCw : ∀ i, 0 < Cw i) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h k a b r : ℕ) :
    0 ≤ hughesYoungNegativeFarCentralShiftScale
      Cγ Cw j T c u X Y h k a b r := by
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65 : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  unfold hughesYoungNegativeFarCentralShiftScale
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hY)
    (mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungReducedStaticScale_nonneg T c hX hY h k)) h65)

/-- Integrated equation-(65) estimate for the swapped equation-(27) kernel
on one negative source shift. -/
theorem exists_negativeFarShift_norm_dfiEquation27CentralIntegral_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r → 0 < q →
      -(r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralIntegral b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)))) r‖ ≤
        Y * hughesYoungCentralLogProfile Y X b a q ^ 2 *
          ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hpoint⟩ :=
    exists_negativeFarShift_norm_dfiEquation27C_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hq hfar
  let F : ℝ → ℂ := fun y =>
    dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
        T c u X Y h k (-(r : ℤ)))) y (y - (r : ℝ))
  let A : ℝ := (P / (5 * T)) ^ j
  let B : ℝ := hughesYoungCentralLogProfile Y X b a q ^ 2 *
    ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
      hughesYoungEquation65Bound Cγ Cw j T c u)
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw j :=
    hughesYoungHeightInputDerivativeConstant_pos hCw j
  have h65nonneg : 0 ≤ hughesYoungEquation65Bound Cγ Cw j T c u := by
    unfold hughesYoungEquation65Bound
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg (by positivity)
          (hughesYoungReducedStaticScale_nonneg T c hX0.le hY0.le h k))
        h65nonneg)
  have hscalePoint : ∀ y : ℝ,
      ‖hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k (y - (r : ℝ)) y‖ ≤
          hughesYoungReducedStaticScale T c X Y h k := by
    intro y
    by_cases hs : hughesYoungReducedLocalizedStaticWeight
        T c u X Y h k (y - (r : ℝ)) y = 0
    · simp [hs, hughesYoungReducedStaticScale_nonneg T c hX0.le hY0.le]
    · have hmem := hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
        hX0 hY0 hs
      exact norm_hughesYoungReducedLocalizedStaticWeight_le_scale
        hX0 hY0 hmem.1.1 hmem.2.1 hh hk hc
  have hweighted : ∀ y : ℝ, ‖(A : ℂ) * F y‖ ≤ B := by
    intro y
    have hp := hpoint j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := r) (q := q) (y := y)
      hT hc hc1 hu hP hPT hX hY ha hb hr hq hfar
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    change A * ‖F y‖ ≤ B
    calc
      A * ‖F y‖ ≤ hughesYoungCentralLogProfile Y X b a q ^ 2 *
          ((1 / T) *
            ‖hughesYoungReducedLocalizedStaticWeight
              T c u X Y h k (y - (r : ℝ)) y‖ *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        simpa only [A, F] using hp
      _ ≤ hughesYoungCentralLogProfile Y X b a q ^ 2 *
          ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
            hughesYoungEquation65Bound Cγ Cw j T c u) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hscalePoint y) (by positivity))
          h65nonneg
      _ = B := by rfl
  have hsupport : ∀ y ∉ Set.Icc Y (2 * Y), (A : ℂ) * F y = 0 := by
    intro y hy
    have hw : hughesYoungReducedCleanedShiftWeight
        T c u X Y h k (-(r : ℤ)) (y - (r : ℝ)) y = 0 := by
      by_contra hn
      have hs : hughesYoungReducedLocalizedStaticWeight
          T c u X Y h k (y - (r : ℝ)) y ≠ 0 := by
        intro hz
        apply hn
        unfold hughesYoungReducedCleanedShiftWeight
        rw [hz]
        norm_num
      exact hy (hughesYoungReducedLocalizedStaticWeight_mem_dyadicBox
        hX0 hY0 hs).2
    simp [F, dfiEquation27C, dfiSwapWeight, hw]
  have hint : (∫ y : ℝ, (A : ℂ) * F y) =
      ∫ y in Set.Icc Y (2 * Y), (A : ℂ) * F y := by
    symm
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hsupport
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc Y (2 * Y)) (C := B)
    (f := fun y => (A : ℂ) * F y) measure_Icc_lt_top
    (fun y _hy => hweighted y)
  rw [Real.volume_real_Icc_of_le (by linarith : Y ≤ 2 * Y)] at hset
  have hnormIntegral :
      ‖∫ y : ℝ, (A : ℂ) * F y‖ ≤ B * Y := by
    rw [hint]
    convert hset using 1
    ring
  rw [MeasureTheory.integral_const_mul, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg hA] at hnormIntegral
  have hfinal : A * ‖∫ y : ℝ, F y‖ ≤ Y * B :=
    hnormIntegral.trans_eq (by ring)
  dsimp only [A, B, F] at hfinal
  unfold dfiEquation27CentralIntegral
  exact hfinal.trans_eq (by ring)

/-- One negative signed central summand has the swapped inverse-square
modulus profile and arbitrary-order equation-(65) decay. -/
theorem exists_negativeFarShift_norm_dfiEquation27CentralSummand_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r q : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r →
      -(r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralSummand b a r
            (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)))) q‖ ≤
        hughesYoungNegativeFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            hughesYoungCentralModulusProfile Y X b a q := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hintegral⟩ :=
    exists_negativeFarShift_norm_dfiEquation27CentralIntegral_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r q hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hfar
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient,
      hughesYoungCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    have hInt := hintegral j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) (r := r) (q := q)
      hT hc hc1 hu hP hPT hX hY hh hk ha hb hr hq hfar
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      b a r q hb ha hr
    have hfreq : 0 ≤ (P / (5 * T)) ^ j := by positivity
    unfold dfiEquation27CentralSummand
    simp only [norm_mul]
    calc
      (P / (5 * T)) ^ j *
          (‖(((b : ℂ) * a)⁻¹)‖ *
            ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
            ‖dfiEquation27CentralIntegral b a
              (dfiReducedDenominator b q) (dfiReducedDenominator a q)
              (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
                T c u X Y h k (-(r : ℤ)))) r‖) =
        ‖(((b : ℂ) * a)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          ((P / (5 * T)) ^ j *
            ‖dfiEquation27CentralIntegral b a
              (dfiReducedDenominator b q) (dfiReducedDenominator a q)
              (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
                T c u X Y h k (-(r : ℤ)))) r‖) := by ring
      _ ≤ ‖(((b : ℂ) * a)⁻¹)‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (Y * hughesYoungCentralLogProfile Y X b a q ^ 2 *
            ((1 / T) * hughesYoungReducedStaticScale T c X Y h k *
              hughesYoungEquation65Bound Cγ Cw j T c u)) := by
        gcongr
      _ = hughesYoungNegativeFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            hughesYoungCentralModulusProfile Y X b a q := by
        unfold hughesYoungNegativeFarCentralShiftScale
          hughesYoungCentralModulusProfile hughesYoungCentralLogProfile
        ring

/-- The complete swapped equation-(27) series on one negative omitted
shift is absolutely summable and has arbitrary-order equation-(65) decay. -/
theorem exists_negativeFarShift_norm_dfiEquation27CentralSeries_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N r : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b → 0 < r →
      -(r : ℤ) ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiEquation27CentralSeries b a r
            (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ))))‖ ≤
        hughesYoungNegativeFarCentralShiftScale Cγ Cw j
          T c u X Y h k a b r *
            ∑' q : ℕ, hughesYoungCentralModulusProfile Y X b a q := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hsummand⟩ :=
    exists_negativeFarShift_norm_dfiEquation27CentralSummand_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hr hfar
  let A : ℝ := (P / (5 * T)) ^ j
  let D : ℝ := hughesYoungNegativeFarCentralShiftScale Cγ Cw j
    T c u X Y h k a b r
  let f : ℕ → ℂ := fun q => dfiEquation27CentralSummand b a r
    (dfiSwapWeight (hughesYoungReducedCleanedShiftWeight
      T c u X Y h k (-(r : ℤ)))) q
  let g : ℕ → ℝ := fun q => hughesYoungCentralModulusProfile Y X b a q
  have hT0 : 0 < T := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    exact pow_pos (div_pos hP (mul_pos (by norm_num) hT0)) j
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact hughesYoungNegativeFarCentralShiftScale_nonneg Cγ Cw j hT0 hc hCw
      (by linarith) (by linarith) h k a b r
  have hg : Summable g := by
    simpa only [g] using summable_hughesYoungCentralModulusProfile hY hX b a
  have hterm : ∀ q : ℕ, A * ‖f q‖ ≤ D * g q := by
    intro q
    simpa only [A, D, f, g] using
      hsummand j hT hc hc1 hu hP hPT hX hY hh hk ha hb hr hfar
  have hfNorm : Summable (fun q => ‖f q‖) := by
    have hmajor : Summable (fun q => A⁻¹ * (D * g q)) :=
      (hg.mul_left D).mul_left A⁻¹
    apply Summable.of_norm_bounded hmajor
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖f q‖ = A⁻¹ * (A * ‖f q‖) := by
        field_simp
      _ ≤ A⁻¹ * (D * g q) :=
        mul_le_mul_of_nonneg_left (hterm q) (by positivity)
  have hf : Summable f := Summable.of_norm hfNorm
  have hleft : A * ‖∑' q, f q‖ ≤ ∑' q, A * ‖f q‖ := by
    calc
      A * ‖∑' q, f q‖ ≤ A * ∑' q, ‖f q‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hfNorm) hA.le
      _ = ∑' q, A * ‖f q‖ := by rw [tsum_mul_left]
  have hright : (∑' q, A * ‖f q‖) ≤ ∑' q, D * g q := by
    exact Summable.tsum_le_tsum hterm (hfNorm.mul_left A) (hg.mul_left D)
  calc
    A * ‖∑' q, f q‖ ≤ ∑' q, A * ‖f q‖ := hleft
    _ ≤ ∑' q, D * g q := hright
    _ = D * ∑' q, g q := tsum_mul_left

/-- One expression covering the positive and negative equation-(27) tail
majorants without altering the source near/far convention. -/
noncomputable def hughesYoungSignedFarCentralShiftBound
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    (T c u X Y : ℝ) (h k a b : ℕ) (r : ℤ) : ℝ :=
  if 0 ≤ r then
    hughesYoungFarCentralShiftScale Cγ Cw j T c u X Y h k a b r.toNat *
      ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q
  else
    hughesYoungNegativeFarCentralShiftScale Cγ Cw j
        T c u X Y h k a b (-r).toNat *
      ∑' q : ℕ, hughesYoungCentralModulusProfile Y X b a q

theorem hughesYoungSignedFarCentralShiftBound_nonneg
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    {T c u X Y : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hCw : ∀ i, 0 < Cw i) (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y)
    (h k a b : ℕ) (r : ℤ) :
    0 ≤ hughesYoungSignedFarCentralShiftBound
      Cγ Cw j T c u X Y h k a b r := by
  unfold hughesYoungSignedFarCentralShiftBound
  split_ifs with hr
  · exact mul_nonneg
      (hughesYoungFarCentralShiftScale_nonneg Cγ Cw j hT hc hCw
        (by linarith) (by linarith) h k a b r.toNat)
      (tsum_nonneg fun q => by
        by_cases hq : q = 0
        · subst q
          simp [hughesYoungCentralModulusProfile]
        · exact hughesYoungCentralModulusProfile_nonneg
            (X := X) (Y := Y) (a := a) (b := b) (q := q))
  · exact mul_nonneg
      (hughesYoungNegativeFarCentralShiftScale_nonneg Cγ Cw j hT hc hCw
        (by linarith) (by linarith) h k a b (-r).toNat)
      (tsum_nonneg fun q => by
        by_cases hq : q = 0
        · subst q
          simp [hughesYoungCentralModulusProfile]
        · exact hughesYoungCentralModulusProfile_nonneg
            (X := Y) (Y := X) (a := b) (b := a) (q := q))

/-- Monotonicity of the explicit equation-(65) majorant in the two
constants supplied by the Gamma-ratio and cutoff derivative estimates. -/
theorem hughesYoungEquation65Bound_mono
    {Cγ₁ Cγ₂ : ℝ} {Cw₁ Cw₂ : ℕ → ℝ} {j : ℕ}
    {T c u : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hCw₁ : ∀ i, 0 < Cw₁ i) (hCw₂ : ∀ i, 0 < Cw₂ i)
    (hγ : Cγ₁ ≤ Cγ₂) (hw : ∀ i, Cw₁ i ≤ Cw₂ i) :
    hughesYoungEquation65Bound Cγ₁ Cw₁ j T c u ≤
      hughesYoungEquation65Bound Cγ₂ Cw₂ j T c u := by
  have hlog : 0 ≤ Real.log (4 * T + |u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  have hheight :
      hughesYoungHeightInputDerivativeConstant Cw₁ j ≤
        hughesYoungHeightInputDerivativeConstant Cw₂ j := by
    unfold hughesYoungHeightInputDerivativeConstant
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _
      (hughesYoungRightContourDerivativeConstant_pos (j - i)).le
    exact mul_le_mul_of_nonneg_left (hw i) (Nat.cast_nonneg _)
  have hheight₁ : 0 ≤ hughesYoungHeightInputDerivativeConstant Cw₁ j :=
    (hughesYoungHeightInputDerivativeConstant_pos hCw₁ j).le
  have hheight₂ : 0 ≤ hughesYoungHeightInputDerivativeConstant Cw₂ j :=
    (hughesYoungHeightInputDerivativeConstant_pos hCw₂ j).le
  unfold hughesYoungEquation65Bound
  gcongr

/-- Equation-(65) decay for either sign of one omitted central shift. -/
theorem exists_farShift_norm_dfiSignedCentralSeries_reducedCleaned_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ} {r : ℤ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b →
      r ∈ hughesYoungFarShifts T P X Y a b M N →
      (P / (5 * T)) ^ j *
          ‖dfiSignedCentralSeries a b r
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
        hughesYoungSignedFarCentralShiftBound Cγ Cw j
          T c u X Y h k a b r := by
  obtain ⟨Cγp, hCγp, Cwp, hCwp, hpos⟩ :=
    exists_farShift_norm_dfiEquation27CentralSeries_reducedCleaned_le
  obtain ⟨Cγn, hCγn, Cwn, hCwn, hneg⟩ :=
    exists_negativeFarShift_norm_dfiEquation27CentralSeries_reducedCleaned_le
  let Cγ : ℝ := max Cγp Cγn
  let Cw : ℕ → ℝ := fun i => max (Cwp i) (Cwn i)
  have hCγ : 0 < Cγ := hCγp.trans_le (le_max_left _ _)
  have hCw : ∀ i, 0 < Cw i := fun i => hCwp i |>.trans_le (le_max_left _ _)
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N r hT hc hc1 hu hP hPT
    hX hY hh hk ha hb hfar
  have hT0 : 0 < T := by linarith
  have hr0 : r ≠ 0 := (mem_hughesYoungFarShifts_iff.mp hfar).2.1
  have hgammaPos : Cγp ≤ Cγ := le_max_left _ _
  have hgammaNeg : Cγn ≤ Cγ := le_max_right _ _
  have hwPos : ∀ i, Cwp i ≤ Cw i := fun i => le_max_left _ _
  have hwNeg : ∀ i, Cwn i ≤ Cw i := fun i => le_max_right _ _
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        apply hr0
        simp [Nat.eq_zero_of_not_pos hn0]
      have hp := hpos j hT hc hc1 hu hP hPT hX hY hh hk ha hb hn hfar
      have hbound := hughesYoungEquation65Bound_mono
        (j := j) (T := T) (c := c) (u := u)
        hT0 hc hCwp hCw hgammaPos hwPos
      have hscale :
          hughesYoungFarCentralShiftScale Cγp Cwp j
              T c u X Y h k a b n ≤
            hughesYoungFarCentralShiftScale Cγ Cw j
              T c u X Y h k a b n := by
        have hbase : 0 ≤
            (1 / T) * hughesYoungReducedStaticScale T c X Y h k :=
          mul_nonneg (by positivity)
            (hughesYoungReducedStaticScale_nonneg T c
              (by linarith) (by linarith) h k)
        unfold hughesYoungFarCentralShiftScale
        gcongr
      have hprofile : 0 ≤
          ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q :=
        tsum_nonneg fun q => by
          by_cases hq : q = 0
          · subst q
            simp [hughesYoungCentralModulusProfile]
          · exact hughesYoungCentralModulusProfile_nonneg
              (X := X) (Y := Y) (a := a) (b := b) (q := q)
      have hp' := hp.trans (mul_le_mul_of_nonneg_right hscale hprofile)
      simpa [dfiSignedCentralSeries, hughesYoungSignedFarCentralShiftBound]
        using hp'
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hrEq : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hrEq]
      have hp := hneg j hT hc hc1 hu hP hPT hX hY hh hk ha hb hm
        (by simpa only [hrEq] using hfar)
      have hbound := hughesYoungEquation65Bound_mono
        (j := j) (T := T) (c := c) (u := u)
        hT0 hc hCwn hCw hgammaNeg hwNeg
      have hscale :
          hughesYoungNegativeFarCentralShiftScale Cγn Cwn j
              T c u X Y h k a b m ≤
            hughesYoungNegativeFarCentralShiftScale Cγ Cw j
              T c u X Y h k a b m := by
        have hbase : 0 ≤
            (1 / T) * hughesYoungReducedStaticScale T c X Y h k :=
          mul_nonneg (by positivity)
            (hughesYoungReducedStaticScale_nonneg T c
              (by linarith) (by linarith) h k)
        unfold hughesYoungNegativeFarCentralShiftScale
        gcongr
      have hprofile : 0 ≤
          ∑' q : ℕ, hughesYoungCentralModulusProfile Y X b a q :=
        tsum_nonneg fun q => by
          by_cases hq : q = 0
          · subst q
            simp [hughesYoungCentralModulusProfile]
          · exact hughesYoungCentralModulusProfile_nonneg
              (X := Y) (Y := X) (a := b) (b := a) (q := q)
      have hp' := hp.trans (mul_le_mul_of_nonneg_right hscale hprofile)
      simpa [dfiSignedCentralSeries, hughesYoungSignedFarCentralShiftBound, hm.ne']
        using hp'

/-- The complete omitted signed central family is controlled by the exact
finite sum of its positive and negative equation-(65) majorants. -/
theorem exists_norm_hughesYoungFarSignedCentralBox_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b →
      (P / (5 * T)) ^ j *
          ‖hughesYoungFarSignedCentralBox
            T c u P X Y h k a b M N‖ ≤
        ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
          hughesYoungSignedFarCentralShiftBound Cγ Cw j
            T c u X Y h k a b r := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hshift⟩ :=
    exists_farShift_norm_dfiSignedCentralSeries_reducedCleaned_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N hT hc hc1 hu hP hPT
    hX hY hh hk ha hb
  let A : ℝ := (P / (5 * T)) ^ j
  let s : Finset ℤ := hughesYoungFarShifts T P X Y a b M N
  let F : ℤ → ℂ := fun r => dfiSignedCentralSeries a b r
    (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
  let B : ℤ → ℝ := fun r => hughesYoungSignedFarCentralShiftBound
    Cγ Cw j T c u X Y h k a b r
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hterm : ∀ r ∈ s, A * ‖F r‖ ≤ B r := by
    intro r hr
    simpa only [A, s, F, B] using
      hshift j hT hc hc1 hu hP hPT hX hY hh hk ha hb hr
  unfold hughesYoungFarSignedCentralBox
  change A * ‖∑ r ∈ s, F r‖ ≤ ∑ r ∈ s, B r
  calc
    A * ‖∑ r ∈ s, F r‖ ≤ A * ∑ r ∈ s, ‖F r‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hA
    _ = ∑ r ∈ s, A * ‖F r‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ s, B r := by
      exact Finset.sum_le_sum fun r hr => hterm r hr

/-- The ordinate-independent part of one signed omitted-central majorant. -/
noncomputable def hughesYoungSignedFarCentralStaticBound
    (T c X Y : ℝ) (h k a b : ℕ) (r : ℤ) : ℝ :=
  if 0 ≤ r then
    ‖(((a : ℂ) * b)⁻¹)‖ * ((a * b * r.toNat ^ 2 : ℕ) : ℝ) * X *
        ((1 / T) * hughesYoungReducedStaticScale T c X Y h k) *
      ∑' q : ℕ, hughesYoungCentralModulusProfile X Y a b q
  else
    ‖(((b : ℂ) * a)⁻¹)‖ * ((b * a * (-r).toNat ^ 2 : ℕ) : ℝ) * Y *
        ((1 / T) * hughesYoungReducedStaticScale T c X Y h k) *
      ∑' q : ℕ, hughesYoungCentralModulusProfile Y X b a q

theorem hughesYoungSignedFarCentralShiftBound_eq_static_mul_equation65
    (Cγ : ℝ) (Cw : ℕ → ℝ) (j : ℕ)
    (T c u X Y : ℝ) (h k a b : ℕ) (r : ℤ) :
    hughesYoungSignedFarCentralShiftBound Cγ Cw j
        T c u X Y h k a b r =
      hughesYoungSignedFarCentralStaticBound T c X Y h k a b r *
        hughesYoungEquation65Bound Cγ Cw j T c u := by
  unfold hughesYoungSignedFarCentralShiftBound
    hughesYoungSignedFarCentralStaticBound
  split_ifs
  · unfold hughesYoungFarCentralShiftScale
    ring
  · unfold hughesYoungNegativeFarCentralShiftScale
    ring

/-- The exact finite static mass of the omitted signed central shifts. -/
noncomputable def hughesYoungFarSignedCentralStaticMass
    (T c P X Y : ℝ) (h k a b M N : ℕ) : ℝ :=
  ∑ r ∈ hughesYoungFarShifts T P X Y a b M N,
    hughesYoungSignedFarCentralStaticBound T c X Y h k a b r

/-- Pointwise equation-(65) estimate with all ordinate dependence factored
into the one published Fourier envelope. -/
theorem exists_norm_hughesYoungFarSignedCentralBox_le_factored :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c u P X Y : ℝ} {h k a b M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k → 0 < a → 0 < b →
      (P / (5 * T)) ^ j *
          ‖hughesYoungFarSignedCentralBox
            T c u P X Y h k a b M N‖ ≤
        hughesYoungFarSignedCentralStaticMass T c P X Y h k a b M N *
          hughesYoungEquation65Bound Cγ Cw j T c u := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hraw⟩ :=
    exists_norm_hughesYoungFarSignedCentralBox_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u P X Y h k a b M N hT hc hc1 hu hP hPT
    hX hY hh hk ha hb
  have h := hraw j (M := M) (N := N)
    hT hc hc1 hu hP hPT hX hY hh hk ha hb
  exact h.trans_eq (by
    unfold hughesYoungFarSignedCentralStaticMass
    simp_rw [hughesYoungSignedFarCentralShiftBound_eq_static_mul_equation65]
    rw [Finset.sum_mul])

theorem hughesYoungSignedFarCentralStaticBound_nonneg
    {T c X Y : ℝ} (hT : 0 < T) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h k a b : ℕ) (r : ℤ) :
    0 ≤ hughesYoungSignedFarCentralStaticBound T c X Y h k a b r := by
  unfold hughesYoungSignedFarCentralStaticBound
  split_ifs
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hX)
          (mul_nonneg (by positivity)
            (hughesYoungReducedStaticScale_nonneg T c hX hY h k)))
      (tsum_nonneg fun q => hughesYoungCentralModulusProfile_nonneg X Y a b q)
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hY)
          (mul_nonneg (by positivity)
            (hughesYoungReducedStaticScale_nonneg T c hX hY h k)))
      (tsum_nonneg fun q => hughesYoungCentralModulusProfile_nonneg Y X b a q)

theorem hughesYoungFarSignedCentralStaticMass_nonneg
    {T c P X Y : ℝ} (hT : 0 < T) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h k a b M N : ℕ) :
    0 ≤ hughesYoungFarSignedCentralStaticMass
      T c P X Y h k a b M N := by
  unfold hughesYoungFarSignedCentralStaticMass
  exact Finset.sum_nonneg fun r _ =>
    hughesYoungSignedFarCentralStaticBound_nonneg hT hX hY h k a b r

/-- The omitted signed central family is genuinely Bochner integrable on
the compact Hughes--Young Mellin segment.  The proof uses strong
measurability of the unrestricted signed series and equation (65) at order
zero as an integrable majorant; no near-shift continuity hypothesis is
smuggled into this step. -/
theorem intervalIntegrable_mul_hughesYoungFarSignedCentralBox
    {T c H P X Y : ℝ} {h k M N : ℕ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hH : 0 ≤ H) (hHT : H ≤ T / 8)
    (hP : 0 < P) (hPT : P ≤ T)
    (hX : 1 / 2 ≤ X) (hY : 1 / 2 ≤ Y) (hh : 0 < h) (hk : 0 < k) :
    IntervalIntegrable (fun u : ℝ => (T : ℂ) *
      hughesYoungFarSignedCentralBox T c u P X Y h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)
      volume (-H) H := by
  obtain ⟨Cγ, _hCγ, Cw, hCw, hpoint⟩ :=
    exists_norm_hughesYoungFarSignedCentralBox_le_factored
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let S : ℝ → ℂ := fun u =>
    hughesYoungFarSignedCentralBox T c u P X Y h k a b M N
  let K : ℝ := hughesYoungFarSignedCentralStaticMass
    T c P X Y h k a b M N
  let E : ℝ → ℝ := fun u =>
    hughesYoungEquation65Bound Cγ Cw 0 T c u
  let F : ℝ → ℂ := fun u => (T : ℂ) * S u
  let G : ℝ → ℝ := fun u => T * K * E u
  have hT0 : 0 < T := by linarith
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hSmeas : AEStronglyMeasurable S := by
    dsimp only [S, a, b]
    exact aestronglyMeasurable_hughesYoungFarSignedCentralBox
      hT0 hc (by linarith) (by linarith) hh hk M N
  have hFmeas : AEStronglyMeasurable F := by
    dsimp only [F]
    exact hSmeas.const_mul (T : ℂ)
  have hEcont : Continuous E := by
    dsimp only [E]
    exact continuous_hughesYoungEquation65Bound Cγ Cw 0 hT0.le c
  have hGcont : Continuous G := continuous_const.mul hEcont
  have hGint : IntervalIntegrable G volume (-H) H :=
    hGcont.intervalIntegrable _ _
  rw [intervalIntegrable_iff] at hGint ⊢
  refine hGint.mono' hFmeas.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have hu' := uIoc_subset_uIcc hu
  have horder : -H ≤ H := by linarith
  have huIcc : Set.uIcc (-H) H = Set.Icc (-H) H := by
    simp only [Set.uIcc, min_eq_left horder, max_eq_right horder]
  rw [huIcc] at hu'
  have huAbs : |u| ≤ H := by
    rw [abs_le]
    exact ⟨hu'.1, hu'.2⟩
  have hp := hpoint 0 (T := T) (c := c) (u := u) (P := P)
    (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
    (M := M) (N := N) hT hc hc1 (huAbs.trans hHT)
    hP hPT hX hY hh hk ha hb
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact hughesYoungFarSignedCentralStaticMass_nonneg hT0
      (by linarith) (by linarith) h k a b M N
  have hE : 0 ≤ E u := by
    have hderiv : 0 < hughesYoungHeightInputDerivativeConstant Cw 0 :=
      hughesYoungHeightInputDerivativeConstant_pos hCw 0
    dsimp only [E]
    unfold hughesYoungEquation65Bound
    positivity
  dsimp only [F, S, G]
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  have hp' :
      ‖hughesYoungFarSignedCentralBox T c u P X Y h k a b M N‖ ≤
        K * E u := by
    simpa only [pow_zero, one_mul, K, E] using hp
  simpa only [a, b, mul_assoc] using
    (mul_le_mul_of_nonneg_left hp' hT0.le)

/-- On a genuine large DFI box the retained near-shift central family is
continuous, hence integrable on the compact Mellin segment. -/
theorem intervalIntegrable_mul_hughesYoungNearSignedCentralBox
    {T c H P U X Y : ℝ} {h k M N : ℕ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hh : 0 < h) (hk : 0 < k)
    (hP : 1 ≤ P) (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    IntervalIntegrable (fun u : ℝ => (T : ℂ) *
      ∑ r ∈ hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
      volume (-H) H := by
  have hs : ∀ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P := by
    intro r hr
    obtain ⟨hr0, hrY, hrP, _hrPos, _hrNeg⟩ :=
      hughesYoungNearShifts_dfi_conditions r hr
    exact ⟨hr0, hrY, hrP⟩
  exact (continuous_const.mul
    (continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
      (by linarith) hc hc1 hX hY hh hk hP hU hscale hs)).intervalIntegrable _ _

/-- The full finite nonzero-shift central family is integrable because it
is exactly the sum of the continuous near family and the measurable,
equation-(65)-dominated far family. -/
theorem intervalIntegrable_mul_hughesYoungFiniteCompleteSignedCentralBox
    {T c H P U X Y : ℝ} {h k M N : ℕ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hH : 0 ≤ H) (hHT : H ≤ T / 8)
    (hP0 : 0 < P) (hPT : P ≤ T)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hh : 0 < h) (hk : 0 < k)
    (hP : 1 ≤ P) (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    IntervalIntegrable (fun u : ℝ => (T : ℂ) *
      hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)
      volume (-H) H := by
  let near : ℝ → ℂ := fun u => (T : ℂ) *
    ∑ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
  let far : ℝ → ℂ := fun u => (T : ℂ) *
    hughesYoungFarSignedCentralBox T c u P X Y h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N
  have hnear : IntervalIntegrable near volume (-H) H := by
    dsimp only [near]
    exact intervalIntegrable_mul_hughesYoungNearSignedCentralBox
      hT hc hc1 hX hY hh hk hP hU hscale
  have hfar : IntervalIntegrable far volume (-H) H := by
    dsimp only [far]
    exact intervalIntegrable_mul_hughesYoungFarSignedCentralBox
      hT hc hc1 hH hHT hP0 hPT (by linarith) (by linarith) hh hk
  have heq : (fun u : ℝ => (T : ℂ) *
      hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) =
      fun u => near u + far u := by
    funext u
    rw [hughesYoungFiniteCompleteSignedCentralBox_eq_near_add_far]
    dsimp only [near, far]
    ring
  rw [heq]
  exact hnear.add hfar

/-- Exact Hughes--Young equation-(81) extension: the integrated retained
near family is the complete finite signed central term minus the integrated
equation-(65) tail.  All integrability hypotheses are discharged from the
actual large-box conditions. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    {T c H P U X Y : ℝ} {h k M N : ℕ}
    (hT : 16 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hH : 0 ≤ H) (hHT : H ≤ T / 8)
    (hP0 : 0 < P) (hPT : P ≤ T)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hh : 0 < h) (hk : 0 < k)
    (hP : 1 ≤ P) (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y) :
    hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N =
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T c H X Y h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N -
        hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k
          (hughesYoungFarShifts T P X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) := by
  rw [hughesYoungNearPointwiseSignedCentralBox_eq_complete_sub_far]
  have hcomplete :=
    intervalIntegrable_mul_hughesYoungFiniteCompleteSignedCentralBox
      (M := M) (N := N) hT hc hc1 hH hHT hP0 hPT hX hY hh hk
      hP hU hscale
  have hfar := intervalIntegrable_mul_hughesYoungFarSignedCentralBox
    (T := T) (c := c) (H := H) (P := P) (X := X) (Y := Y)
      (h := h) (k := k) (M := M) (N := N) hT hc hc1 hH hHT hP0 hPT
      (by linarith) (by linarith) hh hk
  calc
    (∫ u in -H..H, (T : ℂ) *
        (hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N -
          hughesYoungFarSignedCentralBox T c u P X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)) =
      ∫ u in -H..H,
        ((T : ℂ) * hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) -
          ((T : ℂ) * hughesYoungFarSignedCentralBox T c u P X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hcomplete hfar]
      rfl

/-! ## Global equation-(81) extension on the large DFI family -/

/-- The complete finite signed central contribution, summed over precisely
the boxes on which the native Hughes--Young consumer applies DFI.  Unlike
the retained near-shift object, this definition contains every nonzero
shift occurring in each finite divisor rectangle. -/
noncomputable def hughesYoungActiveLargeDFIIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The equation-(65) signed-central tail over the same large-DFI family.
This is distinct from the original far off-diagonal lattice sum: it is the
central-series term introduced and subtracted when extending equation (81)
to all nonzero shifts. -/
noncomputable def hughesYoungActiveLargeDFIIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))

/-- Global, cancellation-preserving Hughes--Young equation (81).  The
actual near-shift DFI central term is exactly the complete finite central
family minus the signed central tail.  Every entry condition is derived
from membership in `hughesYoungActiveLargeDFIBoxes`; no box certificate is
left as a theorem parameter. -/
theorem hughesYoungActiveLargeDFIPointwiseSignedCentral_eq_complete_sub_tail
    {T P : ℝ} {R K : ℕ}
    (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) :
    hughesYoungActiveLargeDFIPointwiseSignedCentral T P R K =
      hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K -
        hughesYoungActiveLargeDFIIntegratedCentralTail T P R K := by
  classical
  obtain ⟨hc, hc1, _hcinv⟩ := hughesYoungSmallContour_spec hT
  unfold hughesYoungActiveLargeDFIPointwiseSignedCentral
    hughesYoungActiveLargeDFIIntegratedCompleteCentral
    hughesYoungActiveLargeDFIIntegratedCentralTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hhmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hkmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hh : 0 < h :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hbox := (Finset.mem_filter.mp hij).2
  have hi : 0 < ij.1 := hbox.1
  have hj : 0 < ij.2 := hbox.2.1
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ j
  obtain ⟨hscale, _hQ, _hUQ, _hQsq⟩ :=
    hughesYoungDFIOptimalScale_spec
      (lt_of_lt_of_le zero_lt_one hP)
      (by linarith) (by linarith)
      hbox.2.2.2.2.1
  have hU : 0 < hughesYoungDFIOptimalU P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) := by
    linarith [hbox.2.2.1]
  exact hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    hT16 hc hc1 (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT hX hY hh hk
      hP hU hscale

/-- Integrated equation-(65) estimate for the omitted signed DFI central
family.  This is the exact compact-Mellin object occurring in the
Hughes--Young source-order decomposition. -/
theorem exists_norm_hughesYoungIntegratedFarSignedCentral_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ (j : ℕ) {T c H P X Y : ℝ} {h k M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H → H ≤ T / 8 →
      0 < P → P ≤ T → 1 / 2 ≤ X → 1 / 2 ≤ Y →
      0 < h → 0 < k →
      (P / (5 * T)) ^ j *
          ‖hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k
            (hughesYoungFarShifts T P X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)‖ ≤
        T * hughesYoungFarSignedCentralStaticMass
            T c P X Y h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N *
          ∫ u in -H..H, hughesYoungEquation65Bound Cγ Cw j T c u := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hpoint⟩ :=
    exists_norm_hughesYoungFarSignedCentralBox_le_factored
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c H P X Y h k M N hT hc hc1 hH hHT hP hPT
    hX hY hh hk
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  let A : ℝ := (P / (5 * T)) ^ j
  let S : ℝ → ℂ := fun u => hughesYoungFarSignedCentralBox
    T c u P X Y h k a b M N
  let E : ℝ → ℝ := fun u => hughesYoungEquation65Bound Cγ Cw j T c u
  let K : ℝ := hughesYoungFarSignedCentralStaticMass
    T c P X Y h k a b M N
  let F : ℝ → ℂ := fun u => (T : ℂ) * S u
  let G : ℝ → ℝ := fun u => T * K * E u
  have hT0 : 0 < T := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact hughesYoungFarSignedCentralStaticMass_nonneg hT0
      (by linarith) (by linarith) h k a b M N
  have hEcont : Continuous E := by
    dsimp only [E]
    exact continuous_hughesYoungEquation65Bound Cγ Cw j hT0.le c
  have hGcont : Continuous G := continuous_const.mul hEcont
  have horder : -H ≤ H := by linarith
  have hbound : ∀ u ∈ Set.Icc (-H) H, A * ‖F u‖ ≤ G u := by
    intro u hu
    have huAbs : |u| ≤ H := by
      rw [abs_le]
      exact ⟨hu.1, hu.2⟩
    have hp := hpoint j (T := T) (c := c) (u := u) (P := P)
      (X := X) (Y := Y) (h := h) (k := k) (a := a) (b := b)
      (M := M) (N := N) hT hc hc1 (huAbs.trans hHT)
      hP hPT hX hY hh hk ha hb
    dsimp only [A, F, S, G, K]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    calc
      (P / (5 * T)) ^ j *
          (T * ‖hughesYoungFarSignedCentralBox
            T c u P X Y h k a b M N‖) =
        T * ((P / (5 * T)) ^ j *
          ‖hughesYoungFarSignedCentralBox
            T c u P X Y h k a b M N‖) := by ring
      _ ≤ T * (hughesYoungFarSignedCentralStaticMass
          T c P X Y h k a b M N *
            hughesYoungEquation65Bound Cγ Cw j T c u) :=
        mul_le_mul_of_nonneg_left hp hT0.le
      _ = _ := by ring
  unfold hughesYoungIntegratedPointwiseSignedCentral
  change A * ‖∫ u in -H..H, F u‖ ≤
    T * K * ∫ u in -H..H, E u
  calc
    A * ‖∫ u in -H..H, F u‖ ≤
        A * ∫ u in -H..H, ‖F u‖ :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm horder) hA
    _ = ∫ u in -H..H, A * ‖F u‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ u in -H..H, G u := by
      rw [intervalIntegral.integral_of_le horder,
        intervalIntegral.integral_of_le horder]
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => mul_nonneg hA (norm_nonneg _)
      · exact hGcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact hbound u (Set.Ioc_subset_Icc_self hu)
    _ = T * K * ∫ u in -H..H, E u := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul]

/-- The preceding compact-Mellin tail with the Gaussian ordinate integral
evaluated exactly as in the published equation-(65) argument. -/
theorem exists_norm_hughesYoungIntegratedFarSignedCentral_full_bound
    (j : ℕ) :
    ∃ Cγ L : ℝ, 0 < Cγ ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T c H P X Y : ℝ} {h k M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 4 * Cγ * c ≤ 1 →
      0 ≤ H → H ≤ T / 8 → 0 < P → P ≤ T →
      1 / 2 ≤ X → 1 / 2 ≤ Y → 0 < h → 0 < k →
      (P / (5 * T)) ^ j *
          ‖hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k
            (hughesYoungFarShifts T P X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)‖ ≤
        T * hughesYoungFarSignedCentralStaticMass T c P X Y h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N *
          (((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hraw⟩ :=
    exists_norm_hughesYoungIntegratedFarSignedCentral_le
  obtain ⟨L, hL, hgaussian⟩ :=
    exists_intervalIntegral_hughesYoungEquation65Bound_le hCγ hCw j
  refine ⟨Cγ, L, hCγ, hL, Cw, hCw, ?_⟩
  intro T c H P X Y h k M N hT hc hc1 hsmall hH hHT hP hPT
    hX hY hh hk
  have hT0 : 0 < T := by linarith
  have hK : 0 ≤ T * hughesYoungFarSignedCentralStaticMass T c P X Y h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N :=
    mul_nonneg hT0.le
      (hughesYoungFarSignedCentralStaticMass_nonneg hT0
        (by linarith) (by linarith) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)
  exact (hraw j hT hc hc1 hH hHT hP hPT hX hY hh hk).trans
    (mul_le_mul_of_nonneg_left
      (hgaussian (by linarith) hc hc1 hsmall hH) hK)

end RiemannZeta.GuthMaynard
