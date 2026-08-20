import RiemannZeta.GuthMaynard.HughesYoungFiniteCentralSource
import RiemannZeta.GuthMaynard.HughesYoungNative

open Complex Finset MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native cancellation-preserving central assembly

This file performs the exact algebra needed between DFI equation (27) and
Hughes--Young equation (85).  The complete finite rectangular central source
is kept as one signed object.  Every term on which a triangle inequality may
legitimately be used is placed in the separate correction package below.
-/

/-! ## Exact finite-source endpoint separation -/

/-- The same finite signed-shift window as the reassembled rectangle, but
with the pure positive-quadrant Mellin weight of Hughes--Young equation
(83).  The shift family remains signed and is not split by a triangle
inequality. -/
noncomputable def hughesYoungFinitePureSignedCentralAtHeight
    (T t c u : ℝ) (h k a b K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungPureReducedMellinWeight T t c u h k)

/-- The literal endpoint discrepancy between the pure equation-(83) source
and the finite dyadic source.  This definition does not assert that the
discrepancy is small; its later estimate must use the two cutoff endpoints
exhibited by `hughesYoungFiniteReassembledReducedMellinWeight_eq_endpoint`.
-/
noncomputable def hughesYoungFiniteEndpointSignedCentralAtHeight
    (T t c u : ℝ) (h k a b K : ℕ) : ℂ :=
  hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K -
    hughesYoungFiniteReassembledSignedCentralAtHeight T t c u h k a b K

/-- Exact cancellation-preserving endpoint decomposition at a fixed
Mellin ordinate and physical height. -/
theorem hughesYoungFiniteReassembledSignedCentralAtHeight_eq_pure_sub_endpoint
    (T t c u : ℝ) (h k a b K : ℕ) :
    hughesYoungFiniteReassembledSignedCentralAtHeight T t c u h k a b K =
      hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K -
        hughesYoungFiniteEndpointSignedCentralAtHeight T t c u h k a b K := by
  unfold hughesYoungFiniteEndpointSignedCentralAtHeight
  ring

/-- A single nonzero pure signed-central shift is integrable on every
bounded ordinate interval.  The proof passes through the literal
equation-(83) beta integral and then the pole-cancelled equation-(84)
contour series; no integrability is postulated for the DFI series. -/
theorem intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_pure
    {T : ℝ} {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {H : ℝ} (t : ℝ) {h k a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungPureReducedMellinWeight T t c u h k))
      volume (-H) H := by
  cases r with
  | ofNat n =>
    have hn : 0 < n := by
      by_contra hn0
      apply hr
      simp [Nat.eq_zero_of_not_pos hn0]
    have hcont :=
      continuous_hughesYoungEquation84PositiveContourSeries_vertical
        T t h k a b n ha hb hn hc (by linarith)
    have hconst : Continuous (fun _u : ℝ =>
        (hughesYoungHeightWeight T t : ℂ)) := continuous_const
    have hint := (hconst.mul hcont).intervalIntegrable
      (a := -H) (b := H) (μ := volume)
    refine hint.congr ?_
    intro u _hu
    have heq :
        dfiSignedCentralSeries a b (n : ℤ)
            (hughesYoungPureReducedMellinWeight T t c u h k) =
          hughesYoungEquation84PositiveContourSeries T t h k a b n
            ((c : ℂ) + (u : ℂ) * I) := by
      rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
          T t c u a b hn,
        hughesYoungEquation83PositiveCentral_eq_equation84
          T t u hc hcHalf h k a b n,
        hughesYoungEquation84Positive_eq_contourSeries
          T t u hcHalf h k a b hn]
    simpa only [Pi.mul_apply] using
      congrArg (fun z : ℂ => (hughesYoungHeightWeight T t : ℂ) * z) heq.symm
  | negSucc m =>
    let n : ℕ := m + 1
    have hn : 0 < n := by dsimp only [n]; omega
    have hrCast : Int.negSucc m = -(n : ℤ) := by
      dsimp only [n]
      omega
    have hcont :=
      continuous_hughesYoungEquation84NegativeContourSeries_vertical
        T t h k a b n ha hb hn hc (by linarith)
    have hconst : Continuous (fun _u : ℝ =>
        (hughesYoungHeightWeight T t : ℂ)) := continuous_const
    have hint := (hconst.mul hcont).intervalIntegrable
      (a := -H) (b := H) (μ := volume)
    refine hint.congr ?_
    intro u _hu
    have heq :
        dfiSignedCentralSeries a b (-(n : ℤ))
            (hughesYoungPureReducedMellinWeight T t c u h k) =
          hughesYoungEquation84NegativeContourSeries T t h k a b n
            ((c : ℂ) + (u : ℂ) * I) := by
      rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
          T t c u a b hn,
        hughesYoungEquation83NegativeCentral_eq_equation84
          T t u hc hcHalf h k a b n,
        hughesYoungEquation84Negative_eq_contourSeries
          T t u hcHalf h k a b hn]
    rw [hrCast]
    simpa only [Pi.mul_apply] using
      congrArg (fun z : ℂ => (hughesYoungHeightWeight T t : ℂ) * z) heq.symm

/-- Whole-line counterpart of the preceding integrability theorem.  This
is what permits finite shift sums to pass through the Hughes--Young source
contour before the complete `(q,r)` series is formed. -/
theorem integrable_heightWeight_mul_dfiSignedCentralSeries_pure
    {T : ℝ} {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (t : ℝ) {h k a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {r : ℤ} (hr : r ≠ 0) :
    Integrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungPureReducedMellinWeight T t c u h k)) := by
  cases r with
  | ofNat n =>
    have hn : 0 < n := by
      by_contra hn0
      apply hr
      simp [Nat.eq_zero_of_not_pos hn0]
    have hint :=
      (integrable_hughesYoungEquation84PositiveContourSeries_vertical
        T t h k a b n ha hb hn hc (by linarith)).const_mul
          (hughesYoungHeightWeight T t : ℂ)
    refine hint.congr ?_
    filter_upwards with u
    have heq :
        dfiSignedCentralSeries a b (n : ℤ)
            (hughesYoungPureReducedMellinWeight T t c u h k) =
          hughesYoungEquation84PositiveContourSeries T t h k a b n
            ((c : ℂ) + (u : ℂ) * I) := by
      rw [dfiSignedCentralSeries_ofNat_pureReduced_eq_equation83
          T t c u a b hn,
        hughesYoungEquation83PositiveCentral_eq_equation84
          T t u hc hcHalf h k a b n,
        hughesYoungEquation84Positive_eq_contourSeries
          T t u hcHalf h k a b hn]
    exact congrArg (fun z : ℂ => (hughesYoungHeightWeight T t : ℂ) * z)
      heq.symm
  | negSucc m =>
    let n : ℕ := m + 1
    have hn : 0 < n := by dsimp only [n]; omega
    have hrCast : Int.negSucc m = -(n : ℤ) := by
      dsimp only [n]
      omega
    have hint :=
      (integrable_hughesYoungEquation84NegativeContourSeries_vertical
        T t h k a b n ha hb hn hc (by linarith)).const_mul
          (hughesYoungHeightWeight T t : ℂ)
    refine hint.congr ?_
    filter_upwards with u
    have heq :
        dfiSignedCentralSeries a b (-(n : ℤ))
            (hughesYoungPureReducedMellinWeight T t c u h k) =
          hughesYoungEquation84NegativeContourSeries T t h k a b n
            ((c : ℂ) + (u : ℂ) * I) := by
      rw [dfiSignedCentralSeries_neg_pureReduced_eq_equation83
          T t c u a b hn,
        hughesYoungEquation83NegativeCentral_eq_equation84
          T t u hc hcHalf h k a b n,
        hughesYoungEquation84Negative_eq_contourSeries
          T t u hcHalf h k a b hn]
    rw [hrCast]
    exact congrArg (fun z : ℂ => (hughesYoungHeightWeight T t : ℂ) * z)
      heq.symm

/-- One finite signed-shift contribution after its whole small-contour
integral has been translated to the absolutely convergent equation-(84)
source line. -/
noncomputable def hughesYoungFiniteSignedEquation84SourceIntegral
    (T t : ℝ) (h k a b : ℕ) (r : ℤ) : ℂ :=
  if r = 0 then 0
  else if 0 ≤ r then
    (hughesYoungHeightWeight T t : ℂ) *
      ∫ u : ℝ,
        hughesYoungEquation84PositiveContourSeries T t h k a b r.toNat
          ((1 : ℂ) + (u : ℂ) * I)
  else
    (hughesYoungHeightWeight T t : ℂ) *
      ∫ u : ℝ,
        hughesYoungEquation84NegativeContourSeries T t h k a b (-r).toNat
          ((1 : ℂ) + (u : ℂ) * I)

/-- The complete finite shift window on the equation-(84) source line. -/
noncomputable def hughesYoungFiniteEquation84SourceAtHeight
    (T t : ℝ) (h k a b K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r

/-- Exact whole-contour identity for one signed shift. -/
theorem integral_heightWeight_mul_dfiSignedCentralSeries_pure_eq_sourceLine
    {T : ℝ} {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (t : ℝ) {h k a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {r : ℤ} (hr0 : r ≠ 0) :
    (∫ u : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      dfiSignedCentralSeries a b r
        (hughesYoungPureReducedMellinWeight T t c u h k)) =
      hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r := by
  rw [integral_const_mul]
  by_cases hrNonneg : 0 ≤ r
  · have hrNat : 0 < r.toNat := by omega
    have hrCast : r = (r.toNat : ℤ) := by omega
    rw [hughesYoungFiniteSignedEquation84SourceIntegral,
      if_neg hr0, if_pos hrNonneg]
    apply congrArg ((hughesYoungHeightWeight T t : ℂ) * ·)
    rw [hrCast]
    simpa only [Int.toNat_natCast] using
      (integral_dfiSignedCentralSeries_pureReduced_ofNat_eq_sourceLine
        T t h k ha hb hrNat hc hcHalf)
  · have hrNat : 0 < (-r).toNat := by omega
    have hrEq : r = -(((-r).toNat : ℕ) : ℤ) := by omega
    rw [hughesYoungFiniteSignedEquation84SourceIntegral,
      if_neg hr0, if_neg hrNonneg]
    apply congrArg ((hughesYoungHeightWeight T t : ℂ) * ·)
    rw [hrEq]
    simpa only [Int.neg_neg, Int.toNat_natCast] using
      (integral_dfiSignedCentralSeries_pureReduced_neg_eq_sourceLine
        T t h k ha hb hrNat hc hcHalf)

/-- The finite pure DFI source, integrated over the whole small contour,
is exactly the finite signed equation-(84) source-line family. -/
theorem integral_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight_eq_sourceLine
    {T : ℝ} {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (t : ℝ) {h k a b : ℕ} (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    (∫ u : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K) =
      hughesYoungFiniteEquation84SourceAtHeight T t h k a b K := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℤ → ℝ → ℂ := fun r u =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungPureReducedMellinWeight T t c u h k)
  have hf : ∀ r ∈ S, Integrable (f r) := by
    intro r _hrmem
    by_cases hr0 : r = 0
    · simp [f, hr0]
    · simp only [f, hr0, if_false]
      exact integrable_heightWeight_mul_dfiSignedCentralSeries_pure
        hc hcHalf t ha hb hr0
  have hpoint : (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K) =
      fun u => ∑ r ∈ S, f r u := by
    funext u
    unfold hughesYoungFinitePureSignedCentralAtHeight
    simp only [B, S, f, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hrmem
    by_cases hr0 : r = 0 <;> simp [hr0]
  rw [hpoint, MeasureTheory.integral_finsetSum S hf]
  unfold hughesYoungFiniteEquation84SourceAtHeight
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr0 : r = 0
  · simp [f, hr0, hughesYoungFiniteSignedEquation84SourceIntegral]
  · simp only [f, hr0, if_false]
    exact integral_heightWeight_mul_dfiSignedCentralSeries_pure_eq_sourceLine
      hc hcHalf t ha hb hr0
/-- Compact-ordinate integrability of the entire finite pure signed source.
The finite shift sum is retained intact for subsequent cancellation. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
    {T : ℝ} {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    {H : ℝ} (t : ℝ) {h k a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFinitePureSignedCentralAtHeight
          T t c u h k a b K) volume (-H) H := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let f : ℤ → ℝ → ℂ := fun r u =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungPureReducedMellinWeight T t c u h k)
  have hsum : IntervalIntegrable
      (∑ r ∈ hughesYoungShiftInterval a b B B, f r)
      volume (-H) H :=
    IntervalIntegrable.sum (hughesYoungShiftInterval a b B B)
      fun r _hrmem => by
        by_cases hr0 : r = 0
        · simp [f, hr0]
        · simp only [f, hr0, if_false]
          exact intervalIntegrable_heightWeight_mul_dfiSignedCentralSeries_pure
            hc hcHalf t ha hb hr0
  refine hsum.congr ?_
  intro u _hu
  unfold hughesYoungFinitePureSignedCentralAtHeight
  simp only [B, f, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr0 : r = 0 <;> simp [hr0]

/-- The endpoint discrepancy is integrable because both its pure and
finite reassembled sources have independently established compact-ordinate
integrability. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungFiniteEndpointSignedCentralAtHeight
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (hcHalf : c < 1 / 2) {H : ℝ} (hH : 0 ≤ H) (t : ℝ)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (K : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteEndpointSignedCentralAtHeight
          T t c u h k a b K) volume (-H) H := by
  unfold hughesYoungFiniteEndpointSignedCentralAtHeight
  simp_rw [mul_sub]
  exact
    (intervalIntegrable_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
      hc hcHalf t ha hb K).sub
      (intervalIntegrable_heightWeight_mul_hughesYoungFiniteReassembledSignedCentralAtHeight
        hT hc hH t hh hk ha hb K)

/-! ## Whole source line and the honest small-contour tail -/

/-- The finite signed equation-(84) source after the physical-height
integration and the actual mollifier sums.  Its Mellin ordinate has already
been integrated over the whole source line. -/
noncomputable def hughesYoungFiniteEquation84IntegratedSource
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ,
        hughesYoungFiniteEquation84SourceAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K

/-- The pure finite signed source with its Mellin ordinate integrated over
the whole line.  This is deliberately distinct from the finite-rectangle
source, whose ordinate is restricted to `[-T/8,T/8]`. -/
noncomputable def hughesYoungFinitePureWholeIntegratedCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFinitePureSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K

/-- Exact passage of the finite pure signed family to the whole
equation-(84) source line.  Positive and negative shifts remain summed
together; no triangle inequality occurs in this identity. -/
theorem hughesYoungFinitePureWholeIntegratedCentral_eq_equation84Source
    {T : ℝ} (hT : Real.exp 3 ≤ T) (K : ℕ) :
    hughesYoungFinitePureWholeIntegratedCentral T K =
      hughesYoungFiniteEquation84IntegratedSource T K := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  have hlog3 : 3 ≤ Real.log T := by
    rw [← Real.log_exp (3 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 3) hT
  have hlog0 : 0 < Real.log T :=
    (by norm_num : (0 : ℝ) < 3).trans_le hlog3
  have hcThird : hughesYoungSmallContour T ≤ (3 : ℝ)⁻¹ := by
    unfold hughesYoungSmallContour
    exact (inv_le_inv₀ hlog0 (show (0 : ℝ) < 3 by norm_num)).2 hlog3
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    calc
      hughesYoungSmallContour T ≤ (3 : ℝ)⁻¹ := hcThird
      _ < 1 / 2 := by norm_num
  unfold hughesYoungFinitePureWholeIntegratedCentral
    hughesYoungFiniteEquation84IntegratedSource
  apply Finset.sum_congr rfl
  intro h hh
  have hhpos : 0 < h := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1
  apply integral_congr_ae
  filter_upwards [] with t
  exact
    integral_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight_eq_sourceLine
      hc.1 hcHalf t (hughesYoungReducedLeft_pos hhpos)
        (hughesYoungReducedRight_pos hhpos hkpos) K

/-! ## Completion of the signed shift family -/

/-- Hughes--Young's complete signed equation-(84) source at a fixed physical
height.  Both signs are combined before any norm is taken. -/
noncomputable def hughesYoungCompleteEquation84SourceAtHeight
    (T t : ℝ) (h k a b : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    ((∫ u : ℝ,
        hughesYoungEquation84CompletePositiveSourceLine T t h k a b u) +
      ∫ u : ℝ,
        hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u)

/-- The same complete source after the cancellation-preserving continuation
from `Re W = 1` to `Re W = 15/16`. -/
noncomputable def hughesYoungCompleteShiftedCentralAtHeight
    (T t : ℝ) (h k a b : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    ((∫ u : ℝ,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((15 / 16 : ℂ) + (u : ℂ) * I)) +
      ∫ u : ℝ,
        hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((15 / 16 : ℂ) + (u : ℂ) * I))

/-- Exact complete-series continuation for the two signed branches. -/
theorem hughesYoungCompleteEquation84SourceAtHeight_eq_shifted
    (T t : ℝ) {h k a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    hughesYoungCompleteEquation84SourceAtHeight T t h k a b =
      hughesYoungCompleteShiftedCentralAtHeight T t h k a b := by
  unfold hughesYoungCompleteEquation84SourceAtHeight
    hughesYoungCompleteShiftedCentralAtHeight
  rw [integral_hughesYoungEquation84CompletePositiveSourceLine_eq_shiftedContinuation
      T t h k ha hb hab (by norm_num : (0 : ℝ) < 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1 / 4),
    integral_hughesYoungEquation84CompleteNegativeSourceLine_eq_shiftedContinuation
      T t h k ha hb hab (by norm_num : (0 : ℝ) < 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1 / 4)]

/-- The omitted signed-shift tail at a fixed height.  This is the exact
difference between the absolutely convergent complete series and the
finite shift window forced by the dyadic rectangle. -/
noncomputable def hughesYoungFiniteEquation84ShiftTailAtHeight
    (T t : ℝ) (h k a b K : ℕ) : ℂ :=
  hughesYoungCompleteEquation84SourceAtHeight T t h k a b -
    hughesYoungFiniteEquation84SourceAtHeight T t h k a b K

/-- Exact finite-to-complete signed-shift identity at one height. -/
theorem hughesYoungFiniteEquation84SourceAtHeight_eq_complete_sub_shiftTail
    (T t : ℝ) (h k a b K : ℕ) :
    hughesYoungFiniteEquation84SourceAtHeight T t h k a b K =
      hughesYoungCompleteEquation84SourceAtHeight T t h k a b -
        hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b K := by
  unfold hughesYoungFiniteEquation84ShiftTailAtHeight
  ring

/-- The complete continued central source after physical-height integration
and the actual mollifier sums. -/
noncomputable def hughesYoungCompleteShiftedIntegratedCentral
    (T : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ,
        hughesYoungCompleteShiftedCentralAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)

/-- The global signed-shift completion error.  It is kept as the exact
difference until joint integrability of the explicit pointwise tail has
been established. -/
noncomputable def hughesYoungFiniteEquation84IntegratedShiftTail
    (T : ℝ) (K : ℕ) : ℂ :=
  hughesYoungCompleteShiftedIntegratedCentral T -
    hughesYoungFiniteEquation84IntegratedSource T K

/-- Exact global completion of the finite signed-shift source. -/
theorem hughesYoungFiniteEquation84IntegratedSource_eq_complete_sub_shiftTail
    (T : ℝ) (K : ℕ) :
    hughesYoungFiniteEquation84IntegratedSource T K =
      hughesYoungCompleteShiftedIntegratedCentral T -
        hughesYoungFiniteEquation84IntegratedShiftTail T K := by
  unfold hughesYoungFiniteEquation84IntegratedShiftTail
  ring

/-- The finite signed equation-(83) source after the actual mollifier-index,
physical-height, and full small-contour integrations. -/
noncomputable def hughesYoungFinitePureIntegratedCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFinitePureSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K

/-- The literal loss from replacing the finite source contour by the whole
equation-(84) line.  It is an error term, not an equality hidden in a
definition of the main term. -/
noncomputable def hughesYoungFinitePureSmallContourTail
    (T : ℝ) (K : ℕ) : ℂ :=
  hughesYoungFinitePureWholeIntegratedCentral T K -
    hughesYoungFinitePureIntegratedCentral T K

/-- Exact recovery of the finite-contour pure source from its whole-line
counterpart and the explicitly named contour tail. -/
theorem hughesYoungFinitePureIntegratedCentral_eq_whole_sub_tail
    (T : ℝ) (K : ℕ) :
    hughesYoungFinitePureIntegratedCentral T K =
      hughesYoungFinitePureWholeIntegratedCentral T K -
        hughesYoungFinitePureSmallContourTail T K := by
  unfold hughesYoungFinitePureSmallContourTail
  ring

/-- The integrated endpoint discrepancy.  It is kept as the exact
difference until joint `(u,t)` integrability of the explicit pointwise
endpoint source has been established; the pointwise correction above is
the source-facing object that must subsequently be identified with this
difference and estimated. -/
noncomputable def hughesYoungFiniteEndpointIntegratedCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  hughesYoungFinitePureIntegratedCentral T K -
    hughesYoungRectangularIntegratedCompleteCentral T K

/-- Exact finite-to-pure source identity after every integration and
mollifier sum.  The endpoint discrepancy is still a signed family; no
boxwise or shiftwise norm has been introduced. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_pure_sub_endpoint
    (T : ℝ) (K : ℕ) :
    hughesYoungRectangularIntegratedCompleteCentral T K =
      hughesYoungFinitePureIntegratedCentral T K -
        hughesYoungFiniteEndpointIntegratedCentral T K := by
  unfold hughesYoungFiniteEndpointIntegratedCentral
  ring

/-- Exact source-order decomposition of the finite rectangular central
family into the whole equation-(84) source and its two genuine truncation
errors: the small-contour tail and the dyadic endpoint discrepancy. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_equation84Source_sub_tails
    {T : ℝ} (hT : Real.exp 3 ≤ T) (K : ℕ) :
    hughesYoungRectangularIntegratedCompleteCentral T K =
      hughesYoungFiniteEquation84IntegratedSource T K -
        hughesYoungFinitePureSmallContourTail T K -
        hughesYoungFiniteEndpointIntegratedCentral T K := by
  rw [hughesYoungRectangularIntegratedCompleteCentral_eq_pure_sub_endpoint,
    hughesYoungFinitePureIntegratedCentral_eq_whole_sub_tail,
    hughesYoungFinitePureWholeIntegratedCentral_eq_equation84Source hT]

/-- Exact central decomposition after completing the signed shift family
and moving the complete equation-(84) source to the cancellation-preserving
shifted contour.  The three subtracted terms are precisely the shift-window,
small-contour, and dyadic-endpoint errors. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_shifted_sub_threeTails
    {T : ℝ} (hT : Real.exp 3 ≤ T) (K : ℕ) :
    hughesYoungRectangularIntegratedCompleteCentral T K =
      hughesYoungCompleteShiftedIntegratedCentral T -
        hughesYoungFiniteEquation84IntegratedShiftTail T K -
        hughesYoungFinitePureSmallContourTail T K -
        hughesYoungFiniteEndpointIntegratedCentral T K := by
  rw [hughesYoungRectangularIntegratedCompleteCentral_eq_equation84Source_sub_tails
      hT,
    hughesYoungFiniteEquation84IntegratedSource_eq_complete_sub_shiftTail]

/-- All non-main terms left after restoring the complete finite dyadic
rectangle around the large-DFI signed central family.  This is an exact
definition: no estimate or asymptotic identification is built into it. -/
noncomputable def hughesYoungNativeOffDiagonalCorrection
    (T P : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
      hughesYoungInactiveIntegratedCompleteCentral T R K -
      hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K -
      hughesYoungActiveLargeDFIIntegratedCentralTail T P R K +
      hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K +
      hughesYoungActiveLargeDFIFarOffDiagonal T P R K

/-- Exact source-order assembly of the concrete active off-diagonal term.
The first summand is the whole cancellation-preserving finite equation-(85)
source.  The second summand consists only of literal complementary and error
terms already present in the DFI/Hughes--Young decomposition. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_rectangularCentral_add_correction
    {T P : ℝ} (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungRectangularIntegratedCompleteCentral T K +
        hughesYoungNativeOffDiagonalCorrection T P R K := by
  rw [hughesYoungActiveFiniteOffDiagonal_eq_largeDFI_add_nonLargeDFI]
  rw [hughesYoungActiveLargeDFIOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far]
  rw [hughesYoungActiveLargeDFIPointwiseSignedCentral_eq_complete_sub_tail
    hT hT16 hP hPT]
  rw [hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_rectangular_sub_corrections]
  unfold hughesYoungNativeOffDiagonalCorrection
  ring

/-- Norm reduction corresponding to the exact source-order assembly.  The
complete central source is still not split into boxes or signed shifts. -/
theorem norm_hughesYoungActiveFiniteOffDiagonal_le_rectangularCentral_add_correction
    {T P : ℝ} (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) (R K : ℕ) :
    ‖hughesYoungActiveFiniteOffDiagonal T (T / 8) R K‖ ≤
      ‖hughesYoungRectangularIntegratedCompleteCentral T K‖ +
        ‖hughesYoungNativeOffDiagonalCorrection T P R K‖ := by
  rw [hughesYoungActiveFiniteOffDiagonal_eq_rectangularCentral_add_correction
    hT hT16 hP hPT R K]
  exact norm_add_le _ _

end RiemannZeta.GuthMaynard
