import RiemannZeta.GuthMaynard.HughesYoungBoundary

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The isolated smooth endpoint belongs to the far-shift family

Starting the smooth dyadic grid at reduced scale `1 / sqrt 2` turns the
lower endpoint into an ordinary localized box.  Since its only surviving
positive integral coordinate is `1`, every non-diagonal term in a mixed
endpoint box is outside Hughes--Young's near-shift range.
-/

/-- If the right dyadic scale is more than four times the left scale, every
near-shift source sum vanishes.  This is the exact support/comparability
fact used in Hughes--Young before summing the DFI error over boxes. -/
theorem sum_hughesYoungNearShifts_eq_zero_of_four_mul_left_lt_right
    {T c H P X Y : ℝ} {h k a b M N : ℕ}
    (hh : 0 < h) (hX : 0 < X) (hY : 0 < Y) (hXY : 4 * X < Y) :
    (∑ r ∈ hughesYoungNearShifts T P X Y a b M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        a b M N r) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r hr
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · rw [if_pos hs]
    by_cases hw : hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k
        (a * m) (b * n) = 0
    · simp [hw]
    · obtain ⟨_hxLower, hxUpper, hyLower, _hyUpper⟩ :=
        hughesYoungGCDReducedIntegratedBoxWeight_ne_zero_bounds
          hh hX hY hw
      have hshift : ((a * m : ℕ) : ℝ) - ((b * n : ℕ) : ℝ) = (r : ℝ) := by
        unfold quadraticDivisorShift at hs
        exact_mod_cast hs
      norm_num [Nat.cast_mul] at hshift
      have hrneg : (r : ℝ) < 0 := by linarith
      have hrsmall := (mem_hughesYoungNearShifts_iff.mp hr).2.2.1
      rw [abs_of_neg hrneg] at hrsmall
      exfalso
      linarith
  · simp [hs]

/-- Symmetrically, if the left dyadic scale is more than four times the
right scale, every near-shift source sum vanishes. -/
theorem sum_hughesYoungNearShifts_eq_zero_of_four_mul_right_lt_left
    {T c H P X Y : ℝ} {h k a b M N : ℕ}
    (hh : 0 < h) (hX : 0 < X) (hY : 0 < Y) (hYX : 4 * Y < X) :
    (∑ r ∈ hughesYoungNearShifts T P X Y a b M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        a b M N r) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r hr
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · rw [if_pos hs]
    by_cases hw : hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k
        (a * m) (b * n) = 0
    · simp [hw]
    · obtain ⟨hxLower, _hxUpper, _hyLower, hyUpper⟩ :=
        hughesYoungGCDReducedIntegratedBoxWeight_ne_zero_bounds
          hh hX hY hw
      have hshift : ((a * m : ℕ) : ℝ) - ((b * n : ℕ) : ℝ) = (r : ℝ) := by
        unfold quadraticDivisorShift at hs
        exact_mod_cast hs
      norm_num [Nat.cast_mul] at hshift
      have hrpos : 0 < (r : ℝ) := by linarith
      have hrsmall := (mem_hughesYoungNearShifts_iff.mp hr).2.2.1
      rw [abs_of_pos hrpos] at hrsmall
      exfalso
      linarith
  · simp [hs]

/-- No near shift survives when the left reduced coordinate is localized to
the initial smooth box and the right scale is at least one. -/
theorem sum_hughesYoungNearShifts_initial_left_eq_zero
    {T c H P Y : ℝ} {h k a b M N : ℕ}
    (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hY : 1 ≤ Y) :
    (∑ r ∈ hughesYoungNearShifts T P
        (1 / hughesYoungDyadicRatio) Y a b M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H
          (1 / hughesYoungDyadicRatio) Y h k)
        a b M N r) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r hr
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · simp only [hs, if_true]
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have ham0 : 0 < a * m := Nat.mul_pos ha hm0
    have hbn0 : 0 < b * n := Nat.mul_pos hb hn0
    by_cases ham1 : a * m = 1
    · by_cases hbn1 : b * n = 1
      · have hr0 : r = 0 := by
          unfold quadraticDivisorShift at hs
          omega
        exact ((mem_hughesYoungNearShifts_iff.mp hr).2.1 hr0).elim
      · have hbn2 : 2 ≤ b * n := by omega
        by_cases hcut : hughesYoungDyadicCutoffAt Y ((b * n : ℕ) : ℝ) = 0
        · rw [← Nat.cast_mul, ← Nat.cast_mul]
          rw [hughesYoungGCDReducedIntegratedBoxWeight_eq_zero_of_rightCutoff
              T c H (1 / hughesYoungDyadicRatio) Y hh hcut]
          simp
        · have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
          have hYlt : Y < ((b * n : ℕ) : ℝ) :=
            lt_of_hughesYoungDyadicCutoffAt_ne_zero hYpos hcut
          have hshiftR : (((a * m : ℕ) : ℝ) - ((b * n : ℕ) : ℝ)) =
              (r : ℝ) := by
            unfold quadraticDivisorShift at hs
            exact_mod_cast hs
          have ham1R : (((a * m : ℕ) : ℝ)) = 1 := by exact_mod_cast ham1
          have hbn2R : (2 : ℝ) ≤ ((b * n : ℕ) : ℝ) := by
            exact_mod_cast hbn2
          have hrform : (r : ℝ) = 1 - ((b * n : ℕ) : ℝ) := by
            rw [← hshiftR, ham1R]
          have hrneg : (r : ℝ) < 0 := by rw [hrform]; linarith
          have habs : |(r : ℝ)| = ((b * n : ℕ) : ℝ) - 1 := by
            rw [abs_of_neg hrneg, hrform]
            ring
          have hfar : Y / 2 < ((b * n : ℕ) : ℝ) - 1 := by
            by_cases hY2 : Y < 2
            · linarith
            · have h2Y : 2 ≤ Y := le_of_not_gt hY2
              linarith
          have hnear := (mem_hughesYoungNearShifts_iff.mp hr).2.2.1
          rw [habs] at hnear
          exact (not_lt_of_ge hnear hfar).elim
    · have ham2 : 2 ≤ a * m := by omega
      rw [← Nat.cast_mul, ← Nat.cast_mul]
      rw [hughesYoungGCDReducedIntegratedBoxWeight_initial_left_eq_zero
        T c H Y hh ham2 (((b * n : ℕ) : ℝ))]
      simp
  · simp [hs]

/-- When the right scale is the initial box, the numerical near-shift
condition itself is impossible for a nonzero integral shift. -/
theorem hughesYoungNearShifts_initial_right_eq_empty
    (T P X : ℝ) (a b M N : ℕ) :
    hughesYoungNearShifts T P X (1 / hughesYoungDyadicRatio) a b M N = ∅ := by
  ext r
  constructor
  · intro hr
    exfalso
    obtain ⟨_hrInterval, hr0, hrsmall, _hrHeight, _hrPos, _hrNeg⟩ :=
      mem_hughesYoungNearShifts_iff.mp hr
    have hrNatPos : 0 < r.natAbs := Int.natAbs_pos.mpr hr0
    have hrNatOne : 1 ≤ r.natAbs := Nat.one_le_iff_ne_zero.mpr hrNatPos.ne'
    have hrAbsOne : (1 : ℝ) ≤ |(r : ℝ)| := by
      have hcast : (1 : ℝ) ≤ (r.natAbs : ℝ) := by exact_mod_cast hrNatOne
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have hratioLt : 1 / hughesYoungDyadicRatio < 1 := by
      exact (div_lt_one hughesYoungDyadicRatio_pos).2
        one_lt_hughesYoungDyadicRatio
    linarith
  · intro hr
    simp at hr

/-- The initial-left localized box is exactly its equation-(65) far family. -/
theorem hughesYoungLocalizedOffDiagonalBox_initial_left_eq_far
    {T c H P Y : ℝ} {h k M N : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hY : 1 ≤ Y) :
    hughesYoungLocalizedOffDiagonalBox T c H
        (1 / hughesYoungDyadicRatio) Y h k M N =
      ∑ r ∈ hughesYoungFarShifts T P
          (1 / hughesYoungDyadicRatio) Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H
            (1 / hughesYoungDyadicRatio) Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    T c H P (1 / hughesYoungDyadicRatio) Y hh]
  rw [sum_hughesYoungNearShifts_initial_left_eq_zero
    hh (hughesYoungReducedLeft_pos hh)
      (hughesYoungReducedRight_pos hh hk) hY]
  simp

/-- The symmetric initial-right localized box is also exactly its far
family, now because the near-shift set is empty before inspecting weights. -/
theorem hughesYoungLocalizedOffDiagonalBox_initial_right_eq_far
    {T c H P X : ℝ} {h k M N : ℕ} (hh : 0 < h) :
    hughesYoungLocalizedOffDiagonalBox T c H
        X (1 / hughesYoungDyadicRatio) h k M N =
      ∑ r ∈ hughesYoungFarShifts T P X
          (1 / hughesYoungDyadicRatio)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X
            (1 / hughesYoungDyadicRatio) h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    T c H P X (1 / hughesYoungDyadicRatio) hh]
  rw [hughesYoungNearShifts_initial_right_eq_empty]
  simp

end RiemannZeta.GuthMaynard
