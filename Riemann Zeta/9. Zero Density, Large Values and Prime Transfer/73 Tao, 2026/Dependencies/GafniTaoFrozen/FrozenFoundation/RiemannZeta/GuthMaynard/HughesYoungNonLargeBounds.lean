import RiemannZeta.GuthMaynard.HughesYoungBoxConsumer
import RiemannZeta.GuthMaynard.HughesYoungBoundaryFar
import RiemannZeta.GuthMaynard.HughesYoungPointwiseDFIAssembly
import RiemannZeta.GuthMaynard.HughesYoungActiveDFIConsumer

open Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative routing of complementary Hughes--Young boxes

The complement of the large comparable DFI range must be split before any
norm estimate is taken.  This module starts with the noncomparable branch:
its near-shift sum is identically zero, so the actual localized box is
controlled solely by the arbitrary-order equation-(65) estimate.
-/

/-- Equation-(65)'s far-box majorant after cancelling the positive
`(P/(5T))^j` integration-by-parts factor. -/
noncomputable def hughesYoungCancelledFarBoxMajorant
    (Cw : ℕ → ℝ) (D L : ℝ) (j : ℕ)
    (T P X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  max 0 <| (P / (5 * T)) ^ (-(j : ℤ)) *
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N

theorem norm_hughesYoungLocalizedOffDiagonalBox_le_cancelledFarMajorant_of_scaled
    {Cw : ℕ → ℝ} {D L T P X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hP : 0 < P)
    (hscaled : (P / (5 * T)) ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N) :
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungCancelledFarBoxMajorant
        Cw D L j T P X Y ε h k M N := by
  let q : ℝ := P / (5 * T)
  have hq : 0 < q := div_pos hP (mul_pos (by norm_num) hT)
  have hqj : 0 < q ^ j := pow_pos hq j
  have hmul := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hqj.le)
  have hcancel : (q ^ j)⁻¹ * q ^ j = 1 := inv_mul_cancel₀ hqj.ne'
  have hzinv : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  unfold hughesYoungCancelledFarBoxMajorant
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

/-- A noncomparable regular box is exactly an equation-(65) box.  Both
orientations are included, and every constant comes from the existing
source theorem rather than from a supplied estimate. -/
theorem exists_norm_hughesYoungNoncomparableBox_le_cancelledFarMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T P X Y : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      0 < X → 0 < Y → 0 < h → 0 < k →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (4 * X < Y ∨ 4 * Y < X) →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
        hughesYoungCancelledFarBoxMajorant
          Cw D L j T P X Y ε h k M N := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T P X Y h k M N hT hT16 hP hPT hX hY hh hk hsmall hcomp
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  have heq : hughesYoungLocalizedOffDiagonalBox T
      (hughesYoungSmallContour T) (T / 8) X Y h k M N =
      ∑ r ∈ hughesYoungFarShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T
            (hughesYoungSmallContour T) (T / 8) X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r := by
    rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
      T (hughesYoungSmallContour T) (T / 8) P X Y hh]
    rcases hcomp with hleft | hright
    · rw [sum_hughesYoungNearShifts_eq_zero_of_four_mul_left_lt_right
        hh hX hY hleft]
      simp
    · rw [sum_hughesYoungNearShifts_eq_zero_of_four_mul_right_lt_left
        hh hX hY hright]
      simp
  have hc := hughesYoungSmallContour_spec hT
  have hscaled := hfar (T := T) (c := hughesYoungSmallContour T)
    (H := T / 8) (P := P) (X := X) (Y := Y) (h := h) (k := k)
    (a := hughesYoungReducedLeft h k) (b := hughesYoungReducedRight h k)
    (M := M) (N := N) hT16 hc.1 hc.2.1 hsmall
      (by positivity) le_rfl hP0 hPT hX hY hh hk ha hb
  apply norm_hughesYoungLocalizedOffDiagonalBox_le_cancelledFarMajorant_of_scaled
    hT0 hP0
  rw [heq]
  simpa only [hughesYoungFarBoxMajorant] using hscaled

/-- In a comparable small-optimal-scale box, both physical scales are at
most `320P`.  The existing arbitrary-order equation-(65) consumer is then
attached to the actual box.  The two scale inequalities are part of the
conclusion because they are what converts its cancelled factor into a
negative power of the global height in the subsequent finite summation. -/
theorem exists_norm_hughesYoungComparableSmallBox_le_smallMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T P X Y : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      0 < X → 1 ≤ Y → 0 < h → 0 < k →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      X ≤ 4 * Y → Y ≤ 4 * X →
      hughesYoungDFIOptimalU P X Y < 64 →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
          hughesYoungSmallBoxMajorant Cw D L j T X Y ε h k M N ∧
        X < 320 * P ∧ Y < 320 * P := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hscaled⟩ :=
    exists_hughesYoungLocalizedOffDiagonalBox_smallScale_scaled_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T P X Y h k M N hT hT16 hP hPT hX hY hh hk hsmall
    hXY hYX hU
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hscaled' := hscaled (T := T) (H := T / 8) (X := X) (Y := Y)
    (h := h) (k := k) (M := M) (N := N) hT hT16 hsmall
      (by positivity) le_rfl hX hY hh hk
  refine ⟨norm_hughesYoungLocalizedOffDiagonalBox_le_smallMajorant_of_scaled
      hT0 hY0 hscaled', ?_, ?_⟩
  · exact hughesYoung_firstScale_lt_threeHundredTwenty_mul_of_optimalU_lt
      (lt_of_lt_of_le zero_lt_one hP) hX hY0 hXY hU
  · exact hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
      (lt_of_lt_of_le zero_lt_one hP) hX hY0 hYX hU

/-- The literal case-by-case majorant for one member of the non-large DFI
complement.  Its branch order mirrors the analytic proof: endpoints first,
then support-empty boxes, comparable small boxes, and finally genuinely
noncomparable equation-(65) boxes. -/
noncomputable def hughesYoungNonLargeBoxCaseMajorant
    (CwLeft CwRight CwSmall CwFar : ℕ → ℝ)
    (DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ)
    (j : ℕ) (T P ε : ℝ) (a b h k : ℕ) (ij : ℕ × ℕ) : ℝ :=
  let X := hughesYoungFullDyadicScale ij.1
  let Y := hughesYoungFullDyadicScale ij.2
  let M := hughesYoungFullDyadicBound ij.1
  let N := hughesYoungFullDyadicBound ij.2
  if ij.1 = 0 then
    if ij.2 = 0 then 0
    else hughesYoungBoundaryBoxMajorant CwLeft DLeft LLeft j
      T X Y ε h k M N
  else if ij.2 = 0 then
    hughesYoungBoundaryBoxMajorant CwRight DRight LRight j
      T X Y ε h k M N
  else if ¬ (a : ℝ) ≤ 2 * X ∨ ¬ (b : ℝ) ≤ 2 * Y then 0
  else if X ≤ 4 * Y ∧ Y ≤ 4 * X then
    hughesYoungSmallBoxMajorant CwSmall DSmall LSmall j
      T X Y ε h k M N
  else
    hughesYoungCancelledFarBoxMajorant CwFar DFar LFar j
      T P X Y ε h k M N

/-- Exhaustive quantitative consumer for one actual non-large active box.
No residual classification, support, endpoint, or scale hypothesis is left
to the caller. -/
theorem exists_norm_hughesYoungActiveNonLargeDFIBox_le_caseMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ CγLeft DLeft LLeft CγRight DRight LRight
        CγSmall DSmall LSmall CγFar DFar LFar : ℝ,
      0 < CγLeft ∧ 0 < DLeft ∧ 0 < LLeft ∧
      0 < CγRight ∧ 0 < DRight ∧ 0 < LRight ∧
      0 < CγSmall ∧ 0 < DSmall ∧ 0 < LSmall ∧
      0 < CγFar ∧ 0 < DFar ∧ 0 < LFar ∧
      ∃ CwLeft CwRight CwSmall CwFar : ℕ → ℝ,
        (∀ i, 0 < CwLeft i) ∧ (∀ i, 0 < CwRight i) ∧
        (∀ i, 0 < CwSmall i) ∧ (∀ i, 0 < CwFar i) ∧
      ∀ {T P : ℝ} {a b h k R K : ℕ} {ij : ℕ × ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      0 < h → 0 < k →
      4 * CγLeft * hughesYoungSmallContour T ≤ 1 →
      4 * CγRight * hughesYoungSmallContour T ≤ 1 →
      4 * CγSmall * hughesYoungSmallContour T ≤ 1 →
      4 * CγFar * hughesYoungSmallContour T ≤ 1 →
      a = hughesYoungReducedLeft h k →
      b = hughesYoungReducedRight h k →
      ij ∈ hughesYoungActiveNonLargeDFIBoxes P a b R K →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)‖ ≤
        hughesYoungNonLargeBoxCaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε a b h k ij := by
  obtain ⟨CγLeft, DLeft, LLeft, hCγLeft, hDLeft, hLLeft,
      CwLeft, hCwLeft, hleft⟩ :=
    exists_norm_hughesYoungInitialLeftBox_le_boundaryMajorant ε hε j
  obtain ⟨CγRight, DRight, LRight, hCγRight, hDRight, hLRight,
      CwRight, hCwRight, hright⟩ :=
    exists_norm_hughesYoungInitialRightBox_le_boundaryMajorant ε hε j
  obtain ⟨CγSmall, DSmall, LSmall, hCγSmall, hDSmall, hLSmall,
      CwSmall, hCwSmall, hsmallBox⟩ :=
    exists_norm_hughesYoungComparableSmallBox_le_smallMajorant ε hε j
  obtain ⟨CγFar, DFar, LFar, hCγFar, hDFar, hLFar,
      CwFar, hCwFar, hfarBox⟩ :=
    exists_norm_hughesYoungNoncomparableBox_le_cancelledFarMajorant ε hε j
  refine ⟨CγLeft, DLeft, LLeft, CγRight, DRight, LRight,
    CγSmall, DSmall, LSmall, CγFar, DFar, LFar,
    hCγLeft, hDLeft, hLLeft, hCγRight, hDRight, hLRight,
    hCγSmall, hDSmall, hLSmall, hCγFar, hDFar, hLFar,
    CwLeft, CwRight, CwSmall, CwFar,
    hCwLeft, hCwRight, hCwSmall, hCwFar, ?_⟩
  intro T P a b h k R K ij hT hT16 hP hPT hh hk
    hcontLeft hcontRight hcontSmall hcontFar ha hb hij
  subst a
  subst b
  let X : ℝ := hughesYoungFullDyadicScale ij.1
  let Y : ℝ := hughesYoungFullDyadicScale ij.2
  let M : ℕ := hughesYoungFullDyadicBound ij.1
  let N : ℕ := hughesYoungFullDyadicBound ij.2
  have hcases := hughesYoungActiveNonLargeDFIBoxes_cases hij
  by_cases hi : ij.1 = 0
  · by_cases hj : ij.2 = 0
    · have hijEq : ij = (0, 0) := Prod.ext hi hj
      subst ij
      have hz := hughesYoungLocalizedOffDiagonalBox_initial_initial_eq_zero
        T (hughesYoungSmallContour T) (T / 8)
        (M := hughesYoungFullDyadicBound 0)
        (N := hughesYoungFullDyadicBound 0) hh hk
      have hz' :
          hughesYoungLocalizedOffDiagonalBox
              T (hughesYoungSmallContour T) (T / 8)
              hughesYoungDyadicRatio⁻¹ hughesYoungDyadicRatio⁻¹
              h k (hughesYoungFullDyadicBound 0)
              (hughesYoungFullDyadicBound 0) = 0 := by
        simp only [one_div] at hz
        exact hz
      simp [hughesYoungNonLargeBoxCaseMajorant,
        hughesYoungFullDyadicScale, hz']
    · obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hijEq : ij = (0, l + 1) := Prod.ext hi hl
      subst ij
      simpa [hughesYoungNonLargeBoxCaseMajorant,
          hughesYoungFullDyadicScale] using
        (hleft (M := hughesYoungFullDyadicBound 0)
          (N := hughesYoungFullDyadicBound (l + 1)) hT hT16
          (one_le_hughesYoungFullDyadicScale_succ l) hh hk hcontLeft)
  · by_cases hj : ij.2 = 0
    · obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hijEq : ij = (i + 1, 0) := Prod.ext hiEq hj
      subst ij
      simpa [hughesYoungNonLargeBoxCaseMajorant,
          hughesYoungFullDyadicScale] using
        (hright (M := hughesYoungFullDyadicBound (i + 1))
          (N := hughesYoungFullDyadicBound 0) hT hT16
          (one_le_hughesYoungFullDyadicScale_succ i) hh hk hcontRight)
    · obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi
      obtain ⟨l, hlEq⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have hX : 1 ≤ X := by
        dsimp only [X]
        rw [hiEq]
        exact one_le_hughesYoungFullDyadicScale_succ i
      have hY : 1 ≤ Y := by
        dsimp only [Y]
        rw [hlEq]
        exact one_le_hughesYoungFullDyadicScale_succ l
      have hX0 : 0 < X := zero_lt_one.trans_le hX
      have hY0 : 0 < Y := zero_lt_one.trans_le hY
      by_cases haX : (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X
      · by_cases hbY : (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y
        · by_cases hcomp : X ≤ 4 * Y ∧ Y ≤ 4 * X
          · have hU : hughesYoungDFIOptimalU P X Y < 64 := by
              rcases hcases with hzeroI | hzeroJ | hbadA | hbadB |
                  hsmall | hleftFar | hrightFar
              · exact False.elim (hi hzeroI)
              · exact False.elim (hj hzeroJ)
              · exact False.elim (hbadA haX)
              · exact False.elim (hbadB hbY)
              · exact hsmall
              · exact False.elim ((not_lt_of_ge hcomp.1) hleftFar)
              · exact False.elim ((not_lt_of_ge hcomp.2) hrightFar)
            have hs := hsmallBox (M := M) (N := N)
              hT hT16 hP hPT hX0 hY hh hk
              hcontSmall hcomp.1 hcomp.2 hU
            have hsupport :
                ¬ (¬ (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X ∨
                  ¬ (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y) :=
              not_or.mpr ⟨not_not.mpr haX, not_not.mpr hbY⟩
            unfold hughesYoungNonLargeBoxCaseMajorant
            rw [if_neg hi, if_neg hj, if_neg hsupport, if_pos hcomp]
            exact hs.1
          · have hfar : 4 * X < Y ∨ 4 * Y < X := by
              rcases not_and_or.mp hcomp with hleftComp | hrightComp
              · exact Or.inr (lt_of_not_ge hleftComp)
              · exact Or.inl (lt_of_not_ge hrightComp)
            have hf := hfarBox (M := M) (N := N)
              hT hT16 hP hPT hX0 hY0 hh hk
              hcontFar hfar
            have hsupport :
                ¬ (¬ (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X ∨
                  ¬ (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y) :=
              not_or.mpr ⟨not_not.mpr haX, not_not.mpr hbY⟩
            unfold hughesYoungNonLargeBoxCaseMajorant
            rw [if_neg hi, if_neg hj, if_neg hsupport, if_neg hcomp]
            exact hf
        · have hz := hughesYoungLocalizedOffDiagonalBox_eq_zero_of_right_scale
            (X := X) (M := M) (N := N)
            T (hughesYoungSmallContour T) (T / 8) hY0 hh
              (lt_of_not_ge hbY)
          have hsupport :
              ¬ (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X ∨
                ¬ (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y :=
            Or.inr hbY
          unfold hughesYoungNonLargeBoxCaseMajorant
          rw [if_neg hi, if_neg hj, if_pos hsupport, hz, norm_zero]
      · have hz := hughesYoungLocalizedOffDiagonalBox_eq_zero_of_left_scale
          (Y := Y) (M := M) (N := N)
          T (hughesYoungSmallContour T) (T / 8) hX0 hh
            (lt_of_not_ge haX)
        have hsupport :
            ¬ (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X ∨
              ¬ (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y :=
          Or.inl haX
        unfold hughesYoungNonLargeBoxCaseMajorant
        rw [if_neg hi, if_neg hj, if_pos hsupport, hz, norm_zero]

/-- The literal sum of the exhaustive one-box majorants over the same
finite family which defines the active non-large DFI contribution. -/
noncomputable def hughesYoungActiveNonLargeDFICaseMajorant
    (CwLeft CwRight CwSmall CwFar : ℕ → ℝ)
    (DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ)
    (j : ℕ) (T P ε : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNonLargeBoxCaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) h k ij

/-- Summation of a pointwise exhaustive non-large-box estimate.  The
indexing finsets on the two sides are definitionally identical, so no
enlargement or unproved counting assertion enters this step. -/
theorem norm_hughesYoungActiveNonLargeDFIOffDiagonal_le_caseMajorant
    {CwLeft CwRight CwSmall CwFar : ℕ → ℝ}
    {DLeft LLeft DRight LRight DSmall LSmall DFar LFar : ℝ}
    {j : ℕ} {T P ε : ℝ} {R K : ℕ}
    (hbox : ∀ {h k : ℕ} {ij : ℕ × ℕ},
      h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2) →
      k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2) →
      ij ∈ hughesYoungActiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)‖ ≤
        hughesYoungNonLargeBoxCaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) h k ij) :
    ‖hughesYoungActiveNonLargeDFIOffDiagonal T P R K‖ ≤
      hughesYoungActiveNonLargeDFICaseMajorant
        CwLeft CwRight CwSmall CwFar
        DLeft LLeft DRight LRight DSmall LSmall DFar LFar
        j T P ε R K := by
  classical
  unfold hughesYoungActiveNonLargeDFIOffDiagonal
    hughesYoungActiveNonLargeDFICaseMajorant
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K,
            hughesYoungLocalizedOffDiagonalBox T
              (hughesYoungSmallContour T) (T / 8)
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ ≤
        ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
                (hughesYoungReducedLeft h k)
                (hughesYoungReducedRight h k) R K,
              ‖hughesYoungLocalizedOffDiagonalBox T
                (hughesYoungSmallContour T) (T / 8)
                (hughesYoungFullDyadicScale ij.1)
                (hughesYoungFullDyadicScale ij.2) h k
                (hughesYoungFullDyadicBound ij.1)
                (hughesYoungFullDyadicBound ij.2)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
          norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ij hij
      exact hbox hh hk hij

/-- Fully quantified non-large correction estimate obtained by combining
the four analytic box estimates and summing their exhaustive case split. -/
theorem exists_norm_hughesYoungActiveNonLargeDFIOffDiagonal_le_caseMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ CγLeft DLeft LLeft CγRight DRight LRight
        CγSmall DSmall LSmall CγFar DFar LFar : ℝ,
      0 < CγLeft ∧ 0 < DLeft ∧ 0 < LLeft ∧
      0 < CγRight ∧ 0 < DRight ∧ 0 < LRight ∧
      0 < CγSmall ∧ 0 < DSmall ∧ 0 < LSmall ∧
      0 < CγFar ∧ 0 < DFar ∧ 0 < LFar ∧
      ∃ CwLeft CwRight CwSmall CwFar : ℕ → ℝ,
        (∀ i, 0 < CwLeft i) ∧ (∀ i, 0 < CwRight i) ∧
        (∀ i, 0 < CwSmall i) ∧ (∀ i, 0 < CwFar i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * CγLeft * hughesYoungSmallContour T ≤ 1 →
      4 * CγRight * hughesYoungSmallContour T ≤ 1 →
      4 * CγSmall * hughesYoungSmallContour T ≤ 1 →
      4 * CγFar * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungActiveNonLargeDFIOffDiagonal T P R K‖ ≤
        hughesYoungActiveNonLargeDFICaseMajorant
          CwLeft CwRight CwSmall CwFar
          DLeft LLeft DRight LRight DSmall LSmall DFar LFar
          j T P ε R K := by
  obtain ⟨CγLeft, DLeft, LLeft, CγRight, DRight, LRight,
      CγSmall, DSmall, LSmall, CγFar, DFar, LFar,
      hCγLeft, hDLeft, hLLeft, hCγRight, hDRight, hLRight,
      hCγSmall, hDSmall, hLSmall, hCγFar, hDFar, hLFar,
      CwLeft, CwRight, CwSmall, CwFar,
      hCwLeft, hCwRight, hCwSmall, hCwFar, hbox⟩ :=
    exists_norm_hughesYoungActiveNonLargeDFIBox_le_caseMajorant ε hε j
  refine ⟨CγLeft, DLeft, LLeft, CγRight, DRight, LRight,
    CγSmall, DSmall, LSmall, CγFar, DFar, LFar,
    hCγLeft, hDLeft, hLLeft, hCγRight, hDRight, hLRight,
    hCγSmall, hDSmall, hLSmall, hCγFar, hDFar, hLFar,
    CwLeft, CwRight, CwSmall, CwFar,
    hCwLeft, hCwRight, hCwSmall, hCwFar, ?_⟩
  intro T P R K hT hT16 hP hPT
    hcontLeft hcontRight hcontSmall hcontFar
  apply norm_hughesYoungActiveNonLargeDFIOffDiagonal_le_caseMajorant
  intro h k ij hhmem hkmem hij
  have hh : 0 < h :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  exact hbox hT hT16 hP hPT hh hk
    hcontLeft hcontRight hcontSmall hcontFar rfl rfl hij

end RiemannZeta.GuthMaynard
