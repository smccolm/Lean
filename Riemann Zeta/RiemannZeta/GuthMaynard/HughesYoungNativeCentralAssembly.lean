import RiemannZeta.GuthMaynard.HughesYoungFiniteCentralSource
import RiemannZeta.GuthMaynard.HughesYoungNative
import RiemannZeta.GuthMaynard.HughesYoungQuantitativeCentral

open Asymptotics Complex Filter Finset MeasureTheory Set
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

/-- Uniform bound for the complete two-sign continued central source at
one physical height.  Both source-line integrals are transported to the
shifted line only after their quantitative estimates have been proved. -/
theorem exists_norm_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
    (C : ℝ) (hC : 0 < C)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      t ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤
        2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨A, hA, hpositive⟩ :=
    exists_norm_integral_hughesYoungCompletePositiveCentralContinuation_le_of_heightConstant
      C hC hweight hc hc4 hε
  refine ⟨A, hA, ?_⟩
  intro T t hT ht h k hh hk
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htAbs : |t| ∈ Set.Icc (T / 4) (4 * T) := by
    simpa only [abs_of_nonneg ht0] using ht
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  let D : ℝ := A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
    ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
    (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
      ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
    (c⁻¹ ^ 5 * T ^ (4 * C * c))
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hposSource := hpositive T t hT htAbs hh hk
  have hpos :
      ‖∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((15 / 16 : ℂ) + (u : ℂ) * I)‖ ≤ D := by
    rw [← integral_hughesYoungCompletePositiveCentralContinuation_vertical_eq
      T t h k ha hb]
    simpa only [a, b, D] using hposSource
  have hnegSource := hpositive T (-t) hT
    (by simpa only [abs_neg] using htAbs) hk hh
  have hnegSource' :
      ‖∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D := by
    rw [show (∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I)) =
        ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
          T (-t) k h b a ((1 : ℂ) + (u : ℂ) * I) by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hughesYoungCompleteNegativeCentralContinuation_eq_swap
        T t h k a b ((1 : ℂ) + (u : ℂ) * I)]
    dsimp only at hnegSource ⊢
    rw [hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k,
      hughesYoungLocalizedStaticScalar_swap T h k] at hnegSource
    simpa only [a, b, D, mul_comm, mul_left_comm, mul_assoc] using hnegSource
  have hneg :
      ‖∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((15 / 16 : ℂ) + (u : ℂ) * I)‖ ≤ D := by
    rw [← integral_hughesYoungCompleteNegativeCentralContinuation_vertical_eq
      T t h k ha hb]
    exact hnegSource'
  have hw0 := hughesYoungHeightWeight_nonneg T t
  have hw1 := hughesYoungHeightWeight_le_one T t
  dsimp only [a, b] at hpos hneg ⊢
  unfold hughesYoungCompleteShiftedCentralAtHeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  calc
    hughesYoungHeightWeight T t *
        ‖(∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              ((15 / 16 : ℂ) + (u : ℂ) * I)) +
          ∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              ((15 / 16 : ℂ) + (u : ℂ) * I)‖
        ≤ hughesYoungHeightWeight T t * (D + D) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hpos hneg)
    _ ≤ 1 * (D + D) := mul_le_mul_of_nonneg_right hw1 (add_nonneg hD0 hD0)
    _ = 2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
            (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
          (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
              (hughesYoungReducedLeft h k : ℝ) ^ ε) *
            ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
              (hughesYoungReducedRight h k : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
            dsimp only [D, a, b]
            ring

theorem exists_norm_hughesYoungCompleteShiftedCentralAtHeight_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T t : ℝ), 1 ≤ T →
      t ∈ Set.Icc (T / 4) (4 * T) → ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤
        2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
          (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
            ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
      C hC hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

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

/-- The exact arithmetic mass left by the low-contour central estimate
before choosing `c = 1 / log T`. -/
noncomputable def hughesYoungCompleteCentralArithmeticMass
    (T c ε : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
          (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
        (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
            (hughesYoungReducedLeft h k : ℝ) ^ ε) *
          ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
            (hughesYoungReducedRight h k : ℝ) ^ ε))

theorem hughesYoungCompleteCentralArithmeticMass_nonneg
    (T c ε : ℝ) :
    0 ≤ hughesYoungCompleteCentralArithmeticMass T c ε := by
  unfold hughesYoungCompleteCentralArithmeticMass
  positivity

private theorem central_lowContour_rpow_reassociation
    {a b c ε : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a ^ (c - 1 / 2) * b ^ (c - 1 / 2)) *
        ((a ^ (c / 4) * a ^ ε) * (b ^ (c / 4) * b ^ ε)) =
      (a * b) ^ (-(1 / 2 : ℝ)) *
        (a ^ (5 * c / 4 + ε) * b ^ (5 * c / 4 + ε)) := by
  have haPow :
      a ^ (c - 1 / 2) * a ^ (c / 4) * a ^ ε =
        a ^ (-(1 / 2 : ℝ)) * a ^ (5 * c / 4 + ε) := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha,
      ← Real.rpow_add ha]
    congr 1
    ring
  have hbPow :
      b ^ (c - 1 / 2) * b ^ (c / 4) * b ^ ε =
        b ^ (-(1 / 2 : ℝ)) * b ^ (5 * c / 4 + ε) := by
    rw [← Real.rpow_add hb, ← Real.rpow_add hb,
      ← Real.rpow_add hb]
    congr 1
    ring
  rw [show (a ^ (c - 1 / 2) * b ^ (c - 1 / 2)) *
      ((a ^ (c / 4) * a ^ ε) * (b ^ (c / 4) * b ^ ε)) =
      (a ^ (c - 1 / 2) * a ^ (c / 4) * a ^ ε) *
        (b ^ (c - 1 / 2) * b ^ (c / 4) * b ^ ε) by ring,
    haPow, hbPow, Real.mul_rpow ha.le hb.le]
  ring

private theorem completeCentralArithmeticSummand_smallContour_le
    {ε T : ℝ} (hε : 0 < ε) (hT : Real.exp 5 ≤ T)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hhT : (h : ℝ) ≤ T) (hkT : (k : ℝ) ≤ T) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
        ((hughesYoungReducedLeft h k : ℝ) ^
            (hughesYoungSmallContour T - 1 / 2) *
          (hughesYoungReducedRight h k : ℝ) ^
            (hughesYoungSmallContour T - 1 / 2)) *
        (((hughesYoungReducedLeft h k : ℝ) ^
              (hughesYoungSmallContour T / 4) *
            (hughesYoungReducedLeft h k : ℝ) ^ ε) *
          ((hughesYoungReducedRight h k : ℝ) ^
              (hughesYoungSmallContour T / 4) *
            (hughesYoungReducedRight h k : ℝ) ^ ε)) ≤
      Real.exp (5 / 2) * T ^ (2 * ε) *
        (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
          (1 / Real.pi)) := by
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let c : ℝ := hughesYoungSmallContour T
  let q : ℝ := 5 * c / 4 + ε
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 5)).trans hT
  obtain ⟨hc, _hc1, _hcinv⟩ := hughesYoungSmallContour_spec hT1
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hT0 : 0 < T := (Real.exp_pos 5).trans_le hT
  have haT : (a : ℝ) ≤ T := by
    have hah : a ≤ h := by
      dsimp only [a, hughesYoungReducedLeft, hughesYoungCommonDivisor]
      exact Nat.div_le_self h (Nat.gcd h k)
    have hahR : (a : ℝ) ≤ h := by exact_mod_cast hah
    exact hahR.trans hhT
  have hbT : (b : ℝ) ≤ T := by
    have hbk : b ≤ k := by
      dsimp only [b, hughesYoungReducedRight, hughesYoungCommonDivisor]
      exact Nat.div_le_self k (Nat.gcd h k)
    have hbkR : (b : ℝ) ≤ k := by exact_mod_cast hbk
    exact hbkR.trans hkT
  have hq : 0 ≤ q := by dsimp only [q, c]; positivity
  have haPow : (a : ℝ) ^ q ≤ T ^ q :=
    Real.rpow_le_rpow haR.le haT hq
  have hbPow : (b : ℝ) ^ q ≤ T ^ q :=
    Real.rpow_le_rpow hbR.le hbT hq
  have hsmall : T ^ (5 * c / 4) = Real.exp (5 / 4) := by
    have h := rpow_smallContour_four_mul_eq (5 / 16 : ℝ) hT1
    dsimp only [c]
    convert h using 1 <;> ring_nf
  have hTq : T ^ q = Real.exp (5 / 4) * T ^ ε := by
    dsimp only [q]
    rw [Real.rpow_add hT0, hsmall]
  have hpair : (a : ℝ) ^ q * (b : ℝ) ^ q ≤
      Real.exp (5 / 2) * T ^ (2 * ε) := by
    calc
      (a : ℝ) ^ q * (b : ℝ) ^ q ≤ T ^ q * T ^ q :=
        mul_le_mul haPow hbPow (Real.rpow_nonneg hbR.le q)
          (Real.rpow_nonneg hT0.le q)
      _ = Real.exp (5 / 2) * T ^ (2 * ε) := by
        rw [hTq]
        rw [show (Real.exp (5 / 4) * T ^ ε) *
            (Real.exp (5 / 4) * T ^ ε) =
          (Real.exp (5 / 4) * Real.exp (5 / 4)) *
            (T ^ ε * T ^ ε) by ring,
          ← Real.exp_add, ← Real.rpow_add hT0]
        congr 1 <;> ring_nf
  have hbase := norm_hughesYoungLocalizedStaticScalar_mul_reduced_rpow_eq
    (T := T) hh hk
  change ‖hughesYoungLocalizedStaticScalar T h k‖ *
      ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
      (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
        ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) ≤ _
  have hreassoc :
      ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
        (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
          ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) =
      (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        ((a : ℝ) ^ q * (b : ℝ) ^ q) := by
    simpa only [Nat.cast_mul, q] using
      central_lowContour_rpow_reassociation haR hbR
  have hfullReassoc : ‖hughesYoungLocalizedStaticScalar T h k‖ *
      ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
        (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
          ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        ((((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          ((a : ℝ) ^ q * (b : ℝ) ^ q)) := by
    rw [mul_assoc, hreassoc]
  rw [hfullReassoc, ← mul_assoc]
  have hbase' : ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
        (1 / Real.pi) := by simpa only [a, b] using hbase
  rw [hbase']
  have hmul := mul_le_mul_of_nonneg_left hpair (show
    0 ≤ ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
      ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
      (1 / Real.pi) by positivity)
  exact hmul.trans_eq (by ring)

/-- After the source choice `c = 1/log T`, the exact central arithmetic
mass is the mollifier gcd mass times only the prescribed epsilon power. -/
theorem eventually_hughesYoungCompleteCentralArithmeticMass_smallContour_le
    {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ T : ℝ in atTop,
      hughesYoungCompleteCentralArithmeticMass T
          (hughesYoungSmallContour T) ε ≤
        Real.exp (5 / 2) * T ^ (2 * ε) *
          (hughesYoungMollifierWeightedGCDMass T * (1 / Real.pi)) := by
  filter_upwards [eventually_detectorCutoff_sq_le_rpow,
      Filter.eventually_ge_atTop (Real.exp 5)] with T hcut hT
  have hT1 : 1 ≤ T := by
    rw [← Real.exp_zero]
    exact (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 5)).trans hT
  have hL : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ T := by
    calc
      (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ T ^ (1 / 22 : ℝ) := by
        simpa only [Nat.cast_pow] using hcut
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  unfold hughesYoungCompleteCentralArithmeticMass
  calc
    (∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            ((hughesYoungReducedLeft h k : ℝ) ^
                (hughesYoungSmallContour T - 1 / 2) *
              (hughesYoungReducedRight h k : ℝ) ^
                (hughesYoungSmallContour T - 1 / 2)) *
            (((hughesYoungReducedLeft h k : ℝ) ^
                  (hughesYoungSmallContour T / 4) *
                (hughesYoungReducedLeft h k : ℝ) ^ ε) *
              ((hughesYoungReducedRight h k : ℝ) ^
                  (hughesYoungSmallContour T / 4) *
                (hughesYoungReducedRight h k : ℝ) ^ ε))) ≤
      ∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          Real.exp (5 / 2) * T ^ (2 * ε) *
            (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
              ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
              (1 / Real.pi)) := by
        apply Finset.sum_le_sum
        intro h hh
        apply Finset.sum_le_sum
        intro k hk
        have hhL : (h : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
          exact_mod_cast (Finset.mem_Icc.mp hh).2
        have hkL : (k : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
          exact_mod_cast (Finset.mem_Icc.mp hk).2
        exact completeCentralArithmeticSummand_smallContour_le hε hT
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1)
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
          (hhL.trans hL) (hkL.trans hL)
    _ = Real.exp (5 / 2) * T ^ (2 * ε) *
      (hughesYoungMollifierWeightedGCDMass T * (1 / Real.pi)) := by
        unfold hughesYoungMollifierWeightedGCDMass
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.sum_mul, Finset.mul_sum]

private theorem completeCentralArithmeticSummand_fixedContour_le
    {c ε T : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) (hT : 1 ≤ T)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hhT : (h : ℝ) ≤ T) (hkT : (k : ℝ) ≤ T) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
        ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
          (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
        (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
            (hughesYoungReducedLeft h k : ℝ) ^ ε) *
          ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
            (hughesYoungReducedRight h k : ℝ) ^ ε)) ≤
      T ^ (5 * c / 2 + 2 * ε) *
        (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
          (1 / Real.pi)) := by
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let q : ℝ := 5 * c / 4 + ε
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have haT : (a : ℝ) ≤ T := by
    have hah : a ≤ h := by
      dsimp only [a, hughesYoungReducedLeft, hughesYoungCommonDivisor]
      exact Nat.div_le_self h (Nat.gcd h k)
    have hahR : (a : ℝ) ≤ (h : ℝ) := by exact_mod_cast hah
    exact hahR.trans hhT
  have hbT : (b : ℝ) ≤ T := by
    have hbk : b ≤ k := by
      dsimp only [b, hughesYoungReducedRight, hughesYoungCommonDivisor]
      exact Nat.div_le_self k (Nat.gcd h k)
    have hbkR : (b : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbk
    exact hbkR.trans hkT
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have haPow : (a : ℝ) ^ q ≤ T ^ q := Real.rpow_le_rpow haR.le haT hq
  have hbPow : (b : ℝ) ^ q ≤ T ^ q := Real.rpow_le_rpow hbR.le hbT hq
  have hpair : (a : ℝ) ^ q * (b : ℝ) ^ q ≤ T ^ (5 * c / 2 + 2 * ε) := by
    calc
      (a : ℝ) ^ q * (b : ℝ) ^ q ≤ T ^ q * T ^ q :=
        mul_le_mul haPow hbPow (Real.rpow_nonneg hbR.le q)
          (Real.rpow_nonneg hT0.le q)
      _ = T ^ (5 * c / 2 + 2 * ε) := by
        rw [← Real.rpow_add hT0]
        congr 1
        dsimp only [q]
        ring
  have hbase := norm_hughesYoungLocalizedStaticScalar_mul_reduced_rpow_eq
    (T := T) hh hk
  have hreassoc :
      ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
        (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
          ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) =
      (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        ((a : ℝ) ^ q * (b : ℝ) ^ q) := by
    simpa only [Nat.cast_mul, q] using
      central_lowContour_rpow_reassociation haR hbR
  rw [mul_assoc, hreassoc, ← mul_assoc]
  have hbase' : ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
        (1 / Real.pi) := by simpa only [a, b] using hbase
  rw [hbase']
  exact (mul_le_mul_of_nonneg_left hpair (by positivity)).trans_eq (by ring)

theorem eventually_hughesYoungCompleteCentralArithmeticMass_fixedContour_le
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      hughesYoungCompleteCentralArithmeticMass T c ε ≤
        T ^ (5 * c / 2 + 2 * ε) *
          (hughesYoungMollifierWeightedGCDMass T * (1 / Real.pi)) := by
  filter_upwards [eventually_detectorCutoff_sq_le_rpow,
      Filter.eventually_ge_atTop (1 : ℝ)] with T hcut hT
  have hL : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ T := by
    calc
      (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ T ^ (1 / 22 : ℝ) := by
        simpa only [Nat.cast_pow] using hcut
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := Real.rpow_one T
  unfold hughesYoungCompleteCentralArithmeticMass
  calc
    (∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
              (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
            (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
                (hughesYoungReducedLeft h k : ℝ) ^ ε) *
              ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
                (hughesYoungReducedRight h k : ℝ) ^ ε))) ≤
      ∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          T ^ (5 * c / 2 + 2 * ε) *
            (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
              ((Nat.gcd h k : ℝ) / ((h : ℝ) * (k : ℝ))) *
              (1 / Real.pi)) := by
        apply Finset.sum_le_sum
        intro h hh
        apply Finset.sum_le_sum
        intro k hk
        have hhL : (h : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hh).2
        have hkL : (k : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hk).2
        exact completeCentralArithmeticSummand_fixedContour_le hc hε hT
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1)
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
          (hhL.trans hL) (hkL.trans hL)
    _ = T ^ (5 * c / 2 + 2 * ε) *
        (hughesYoungMollifierWeightedGCDMass T * (1 / Real.pi)) := by
      unfold hughesYoungMollifierWeightedGCDMass
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Finset.sum_mul, Finset.mul_sum]

/-- Physical-height integration costs exactly the length `15T/4` of the
support interval. -/
theorem exists_norm_integral_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
    (C : ℝ) (hC : 0 < C)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : ℝ), 1 ≤ T →
      ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ t : ℝ, hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤
        (15 * T / 4) *
          (2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
            ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
            (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
              ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
            (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
  obtain ⟨A, hA, hpoint⟩ :=
    exists_norm_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
      C hC hweight hc hc4 hε
  refine ⟨A, hA, ?_⟩
  intro T hT h k hh hk
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let D : ℝ := 2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
    ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
    (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
      ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
    (c⁻¹ ^ 5 * T ^ (4 * C * c))
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ ↦ D)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  dsimp only
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) =
        ∫ _t in Set.Icc (T / 4) (4 * T), D by
      exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    dsimp only [D, a, b]
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hzero : hughesYoungCompleteShiftedCentralAtHeight T t h k a b = 0 := by
        unfold hughesYoungCompleteShiftedCentralAtHeight
        simp [hw]
      rw [hzero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ hD0) t
    · have ht := hughesYoungHeightWeight_support hT0 hw
      have hbnd := hpoint T t hT ht hh hk
      change ‖hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤ B t
      have hBt : B t = D := by
        exact Set.indicator_of_mem ht _
      rw [hBt]
      dsimp only [D, a, b] at hbnd ⊢
      exact hbnd

theorem exists_norm_integral_hughesYoungCompleteShiftedCentralAtHeight_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T : ℝ), 1 ≤ T →
      ∀ {h k : ℕ}, 0 < h → 0 < k →
      let a := hughesYoungReducedLeft h k
      let b := hughesYoungReducedRight h k
      ‖∫ t : ℝ, hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤
        (15 * T / 4) *
          (2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
            ((a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2)) *
            (((a : ℝ) ^ (c / 4) * (a : ℝ) ^ ε) *
              ((b : ℝ) ^ (c / 4) * (b : ℝ) ^ ε)) *
            (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_integral_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
      C hC hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

/-- Finite mollifier summation of the complete continued central source. -/
theorem exists_norm_hughesYoungCompleteShiftedIntegratedCentral_le_of_heightConstant
    (C : ℝ) (hC : 0 < C)
    (hweight : ∀ (T t u c : ℝ), 1 ≤ T →
      |t| ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8))
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : ℝ), 1 ≤ T →
      ‖hughesYoungCompleteShiftedIntegratedCentral T‖ ≤
        (15 * T / 4) * (2 * A *
          hughesYoungCompleteCentralArithmeticMass T c ε *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
  obtain ⟨A, hA, hpair⟩ :=
    exists_norm_integral_hughesYoungCompleteShiftedCentralAtHeight_le_of_heightConstant
      C hC hweight hc hc4 hε
  refine ⟨A, hA, ?_⟩
  intro T hT
  classical
  unfold hughesYoungCompleteShiftedIntegratedCentral
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∫ t : ℝ, hughesYoungCompleteShiftedCentralAtHeight T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖∫ t : ℝ, hughesYoungCompleteShiftedCentralAtHeight T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)‖ := by
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun h _hh ↦ norm_sum_le _ _)
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (15 * T / 4) *
            (2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
              ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
                (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
              (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
                  (hughesYoungReducedLeft h k : ℝ) ^ ε) *
                ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
                  (hughesYoungReducedRight h k : ℝ) ^ ε)) *
              (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
        gcongr with h hh k hk
        exact hpair T hT
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hh).1)
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
    _ = (15 * T / 4) * (2 * A *
          hughesYoungCompleteCentralArithmeticMass T c ε *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
        unfold hughesYoungCompleteCentralArithmeticMass
        let P : ℝ := (15 * T / 4) * (2 * A) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))
        rw [show (15 * T / 4) *
            (2 * A *
              (∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
                ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
                  ‖hughesYoungLocalizedStaticScalar T h k‖ *
                    ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
                      (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
                    (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
                        (hughesYoungReducedLeft h k : ℝ) ^ ε) *
                      ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
                        (hughesYoungReducedRight h k : ℝ) ^ ε))) *
              (c⁻¹ ^ 5 * T ^ (4 * C * c))) =
            P * (∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
              ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
                ‖hughesYoungLocalizedStaticScalar T h k‖ *
                  ((hughesYoungReducedLeft h k : ℝ) ^ (c - 1 / 2) *
                    (hughesYoungReducedRight h k : ℝ) ^ (c - 1 / 2)) *
                  (((hughesYoungReducedLeft h k : ℝ) ^ (c / 4) *
                      (hughesYoungReducedLeft h k : ℝ) ^ ε) *
                    ((hughesYoungReducedRight h k : ℝ) ^ (c / 4) *
                      (hughesYoungReducedRight h k : ℝ) ^ ε))) by
              dsimp only [P]
              ring]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        dsimp only [P]
        ring

theorem exists_norm_hughesYoungCompleteShiftedIntegratedCentral_le
    {c ε : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (hε : 0 < ε) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (T : ℝ), 1 ≤ T →
      ‖hughesYoungCompleteShiftedIntegratedCentral T‖ ≤
        (15 * T / 4) * (2 * A *
          hughesYoungCompleteCentralArithmeticMass T c ε *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_hughesYoungCompleteShiftedIntegratedCentral_le_of_heightConstant
      C hC hweight hc hc4 hε
  exact ⟨C, A, hC, hA, hbound⟩

/-- The complete cancellation-preserving Hughes--Young central source has
the required native `T^(1+ε)` size.  The contour is fixed after choosing
the single height-growth exponent, so all implicit constants are uniform
in the physical height. -/
theorem hughesYoungCompleteShiftedIntegratedCentral_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungCompleteShiftedIntegratedCentral T‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_abs_height_power
  let η : ℝ := ε / 20
  let D : ℝ := 4 * C + 5 / 2
  let c : ℝ := min (1 / 8) (ε / (2 * D))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hc4 : c < 1 / 4 :=
    (min_le_left (1 / 8 : ℝ) (ε / (2 * D))).trans_lt (by norm_num)
  have hcD : D * c ≤ ε / 2 := by
    have hcUpper : c ≤ ε / (2 * D) := min_le_right _ _
    calc
      D * c ≤ D * (ε / (2 * D)) := mul_le_mul_of_nonneg_left hcUpper hD.le
      _ = ε / 2 := by field_simp [hD.ne']
  obtain ⟨A, hA, hcentral⟩ :=
    exists_norm_hughesYoungCompleteShiftedIntegratedCentral_le_of_heightConstant
      C hC hweight hc hc4 hη
  have hmass :=
    eventually_hughesYoungCompleteCentralArithmeticMass_fixedContour_le
      hc.le hη
  have hG := hughesYoungMollifierWeightedGCDMass_epsilonPowerBound η hη
  obtain ⟨K, hK0, hK⟩ := hG.exists_nonneg
  have hKbound := hK.bound
  let B : ℝ := (15 / 4) * (2 * A) * c⁻¹ ^ 5 * (1 / Real.pi) * K
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  apply IsBigO.of_bound B
  filter_upwards [hmass, hKbound, Filter.eventually_ge_atTop (1 : ℝ)] with
      T hmassT hKT hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hmass0 : 0 ≤ hughesYoungMollifierWeightedGCDMass T :=
    hughesYoungMollifierWeightedGCDMass_nonneg T
  have hKsimple : hughesYoungMollifierWeightedGCDMass T ≤ K * T ^ η := by
    have hraw := hKT
    simp only [Real.norm_eq_abs, abs_abs, abs_one, mul_one] at hraw
    rw [abs_of_nonneg hmass0, abs_of_nonneg (Real.rpow_nonneg hT0.le η)] at hraw
    exact hraw
  have hexponent : 1 + (5 * c / 2 + 2 * η) + η + 4 * C * c ≤ 1 + ε := by
    have hcontour : (4 * C + 5 / 2) * c ≤ ε / 2 := by
      simpa only [D] using hcD
    dsimp only [η]
    linarith
  have hpow : T ^ (1 + (5 * c / 2 + 2 * η) + η + 4 * C * c) ≤
      T ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hT hexponent
  have hcentralT := hcentral T hT
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  have hpowProduct :
      T ^ (5 * c / 2 + 2 * η) * T ^ η * T ^ (4 * C * c) =
        T ^ ((5 * c / 2 + 2 * η) + η + 4 * C * c) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
  have hheightProduct :
      T * T ^ ((5 * c / 2 + 2 * η) + η + 4 * C * c) =
        T ^ (1 + (5 * c / 2 + 2 * η) + η + 4 * C * c) := by
    calc
      T * T ^ ((5 * c / 2 + 2 * η) + η + 4 * C * c) =
          T ^ (1 : ℝ) * T ^ ((5 * c / 2 + 2 * η) + η + 4 * C * c) := by
            rw [Real.rpow_one]
      _ = T ^ (1 + ((5 * c / 2 + 2 * η) + η + 4 * C * c)) :=
        (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + (5 * c / 2 + 2 * η) + η + 4 * C * c) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg (hughesYoungCompleteShiftedIntegratedCentral T)),
    htarget]
  calc
    ‖hughesYoungCompleteShiftedIntegratedCentral T‖ ≤
        (15 * T / 4) * (2 * A *
          hughesYoungCompleteCentralArithmeticMass T c η *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := hcentralT
    _ ≤ (15 * T / 4) * (2 * A *
          (T ^ (5 * c / 2 + 2 * η) *
            (hughesYoungMollifierWeightedGCDMass T * (1 / Real.pi))) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by gcongr
    _ ≤ (15 * T / 4) * (2 * A *
          (T ^ (5 * c / 2 + 2 * η) *
            ((K * T ^ η) * (1 / Real.pi))) *
          (c⁻¹ ^ 5 * T ^ (4 * C * c))) := by gcongr
    _ = B * T ^ (1 + (5 * c / 2 + 2 * η) + η + 4 * C * c) := by
      calc
        (15 * T / 4) * (2 * A *
            (T ^ (5 * c / 2 + 2 * η) * ((K * T ^ η) * (1 / Real.pi))) *
            (c⁻¹ ^ 5 * T ^ (4 * C * c))) =
            B * (T *
              (T ^ (5 * c / 2 + 2 * η) * T ^ η * T ^ (4 * C * c))) := by
                dsimp only [B]
                ring
        _ = B * (T * T ^ ((5 * c / 2 + 2 * η) + η + 4 * C * c)) := by
          rw [hpowProduct]
        _ = B * T ^ (1 + (5 * c / 2 + 2 * η) + η + 4 * C * c) := by
          rw [hheightProduct]
    _ ≤ B * T ^ (1 + ε) := mul_le_mul_of_nonneg_left hpow hB0

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
