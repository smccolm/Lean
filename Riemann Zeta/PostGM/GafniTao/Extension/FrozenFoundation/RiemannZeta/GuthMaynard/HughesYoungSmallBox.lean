import RiemannZeta.GuthMaynard.HughesYoungBoxConsumer
import RiemannZeta.GuthMaynard.HughesYoungScaleChoice

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The DFI-small dyadic-box branch

For the complementary branch of the optimized DFI scale split, choose the
auxiliary frequency parameter `P = T / (2Y)`.  Since every nonzero integral
shift has absolute value at least one, the corresponding DFI near family is
empty.  Thus the exact source box is the equation-(65) complementary family.
We retain an arbitrary number of integrations by parts; this is essential in
the later dyadic summation and replaces the former provisional `j = 0` bound.
-/

theorem hughesYoungNearShifts_halfUnit_eq_empty
    {T X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) :
    hughesYoungNearShifts T (T / (2 * Y)) X Y a b M N = ∅ := by
  classical
  ext r
  constructor
  · intro hr
    have hdata := (mem_hughesYoungNearShifts_iff.mp hr).2
    have hr0 : r ≠ 0 := hdata.1
    have hrOne : (1 : ℝ) ≤ |(r : ℝ)| := by
      have hint : (1 : ℤ) ≤ |r| := Int.one_le_abs hr0
      exact_mod_cast hint
    have hdiv : 1 / Y ≤ |(r : ℝ)| / Y := by
      exact div_le_div_of_nonneg_right hrOne hY.le
    have hmul : T * (1 / Y) ≤ T * (|(r : ℝ)| / Y) :=
      mul_le_mul_of_nonneg_left hdiv hT.le
    have hnear : T * (|(r : ℝ)| / Y) ≤ T / (2 * Y) := hdata.2.2.1
    have hstrict : T / (2 * Y) < T * (1 / Y) := by
      field_simp [hY.ne']
      linarith
    exfalso
    linarith
  · intro hr
    simp at hr

theorem hughesYoungLocalizedOffDiagonalBox_eq_halfUnit_far
    {T c H X Y : ℝ} {h k M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) (hh : 0 < h) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N =
      ∑ r ∈ hughesYoungFarShifts T (T / (2 * Y)) X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    T c H (T / (2 * Y)) X Y hh]
  rw [hughesYoungNearShifts_halfUnit_eq_empty hT hY]
  simp

/-- The equation-(65) small-scale majorant after cancelling its strictly
positive integration-by-parts prefactor.  The auxiliary frequency is the
source-faithful choice `P = T / (2Y)`. -/
noncomputable def hughesYoungSmallBoxMajorant
    (Cw : ℕ → ℝ) (D L : ℝ) (j : ℕ)
    (T X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  max 0 <| ((T / (2 * Y)) / (5 * T)) ^ (-(j : ℤ)) *
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N

theorem norm_hughesYoungLocalizedOffDiagonalBox_le_smallMajorant_of_scaled
    {Cw : ℕ → ℝ} {D L T X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y)
    (hscaled : ((T / (2 * Y)) / (5 * T)) ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N) :
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungSmallBoxMajorant Cw D L j T X Y ε h k M N := by
  let q : ℝ := (T / (2 * Y)) / (5 * T)
  have hq : 0 < q := div_pos (div_pos hT (mul_pos (by norm_num) hY))
    (mul_pos (by norm_num) hT)
  have hqj : 0 < q ^ j := pow_pos hq j
  have hmul := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hqj.le)
  have hcancel : (q ^ j)⁻¹ * q ^ j = 1 := inv_mul_cancel₀ hqj.ne'
  have hzinv : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  unfold hughesYoungSmallBoxMajorant
  change _ ≤ max 0 (q ^ (-(j : ℤ)) *
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N)
  rw [hzinv]
  apply le_max_of_le_right
  calc
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ =
      (q ^ j)⁻¹ * (q ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (q ^ j)⁻¹ *
        hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := hmul

/-- A source-facing arbitrary-order equation-(65) estimate for one localized
box, after the exact finite shift partition and gcd reduction.  It applies
precisely where the optimized DFI scale is too short for `Q ≥ 8`. -/
theorem exists_hughesYoungLocalizedOffDiagonalBox_smallScale_scaled_bound
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T H X Y : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      0 ≤ H → H ≤ T / 8 → 0 < X → 1 ≤ Y →
      0 < h → 0 < k →
      ((T / (2 * Y)) / (5 * T)) ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) H X Y h k M N‖ ≤
        hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T H X Y h k M N hTexp hT hsmall hH hHT hX hY hh hk
  have hT0 : 0 < T := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  obtain ⟨hc, hc1, _hcinv⟩ := hughesYoungSmallContour_spec hTexp
  have hP : 0 < T / (2 * Y) := div_pos hT0 (mul_pos (by norm_num) hY0)
  have hPT : T / (2 * Y) ≤ T := by
    have hden : 1 ≤ 2 * Y := by
      linarith
    exact (div_le_iff₀ (mul_pos (by norm_num) hY0)).2 (by nlinarith)
  have hbound := hfar (T := T) (c := hughesYoungSmallContour T) (H := H)
    (P := T / (2 * Y)) (X := X) (Y := Y) (h := h) (k := k)
    (a := hughesYoungReducedLeft h k) (b := hughesYoungReducedRight h k)
    (M := M) (N := N) hT hc hc1 hsmall hH hHT hP hPT hX hY0 hh hk
    (hughesYoungReducedLeft_pos hh) (hughesYoungReducedRight_pos hh hk)
  rw [hughesYoungLocalizedOffDiagonalBox_eq_halfUnit_far hT0 hY0 hh]
  exact hbound

end RiemannZeta.GuthMaynard
