import RiemannZeta.GuthMaynard.HughesYoungIntegratedSmallContourTail
import RiemannZeta.GuthMaynard.HughesYoungNativeCorrections
import RiemannZeta.GuthMaynard.HughesYoungShiftTailConsumer
import RiemannZeta.GuthMaynard.HughesYoungActiveNativeAssembly

open Asymptotics Complex Filter

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native Hughes--Young moment assembly

This module contains the final quantitative consumers of the exact AFE,
DFI, and cancellation-preserving central-source identities.  Error terms
are added only after the signed central family has been assembled.
-/

/-! ## Epsilon-dependent source parameters

The source proof chooses its physical truncation and Fourier smoothing only
after the requested epsilon is fixed.  Keeping a fixed positive power in
either parameter would leave a fixed positive power loss and therefore
cannot establish `EpsilonPowerBound`.  The following two definitions make
that quantifier order literal.
-/

/-- Physical AFE radius `T^(2+delta)` used in one epsilon instance. -/
noncomputable def hughesYoungEpsilonRadius (delta T : ℝ) : ℕ :=
  ⌈T ^ (2 + delta)⌉₊

/-- Fourier window `8 T^delta` used in the same epsilon instance. -/
noncomputable def hughesYoungEpsilonSmoothingScale (delta T : ℝ) : ℝ :=
  8 * T ^ delta

theorem hughesYoungEpsilonRadius_pos
    {delta T : ℝ} (hT : 1 ≤ T) :
    0 < hughesYoungEpsilonRadius delta T := by
  unfold hughesYoungEpsilonRadius
  exact Nat.ceil_pos.mpr <| Real.rpow_pos_of_pos
    (zero_lt_one.trans_le hT) (2 + delta)

theorem hughesYoungEpsilonRadius_lower (delta T : ℝ) :
    T ^ (2 + delta) ≤ (hughesYoungEpsilonRadius delta T : ℝ) := by
  unfold hughesYoungEpsilonRadius
  exact Nat.le_ceil _

theorem hughesYoungEpsilonRadius_le_two_mul_rpow
    {delta T : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) :
    (hughesYoungEpsilonRadius delta T : ℝ) ≤
      2 * T ^ (2 + delta) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hexp : 0 ≤ 2 + delta := by linarith
  have hp : 1 ≤ T ^ (2 + delta) := Real.one_le_rpow hT hexp
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hT0.le (2 + delta))
  unfold hughesYoungEpsilonRadius
  linarith

theorem hughesYoungEpsilonRadius_le_two_mul_cube
    {delta T : ℝ} (hT : 1 ≤ T) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    (hughesYoungEpsilonRadius delta T : ℝ) ≤ 2 * T ^ (3 : ℝ) := by
  have hr := hughesYoungEpsilonRadius_le_two_mul_rpow hT hdelta0
  have hp : T ^ (2 + delta) ≤ T ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact hr.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

/-- The existing logarithmic dyadic depth also covers every
epsilon-dependent source radius with `delta ≤ 1`. -/
theorem hughesYoungEpsilonRadius_cover
    {delta T : ℝ} (hT : 2 ≤ T) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) {h k : ℕ}
    (hh : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hk : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    ((((hughesYoungReducedLeft h k) *
      (hughesYoungReducedRight h k) * hughesYoungEpsilonRadius delta T : ℕ) : ℝ)) ≤
        hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
  have hT1 : 1 ≤ T := by linarith
  have hcut := detectorCutoff_le_three_mul T hT1
  have hrr := hughesYoungEpsilonRadius_le_two_mul_cube hT1 hdelta0 hdelta1
  have hh' : (h : ℝ) ≤ (3 * T) ^ 2 := by
    have hhcast : (h : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact hhcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have hk' : (k : ℝ) ≤ (3 * T) ^ 2 := by
    have hkcast : (k : ℝ) ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hkcast.trans (pow_le_pow_left₀ (by positivity) hcut 2)
  have ha : (hughesYoungReducedLeft h k : ℝ) ≤ h := by
    exact_mod_cast hughesYoungReducedLeft_le h k
  have hb : (hughesYoungReducedRight h k : ℝ) ≤ k := by
    exact_mod_cast hughesYoungReducedRight_le h k
  have hraw :
      ((hughesYoungReducedLeft h k : ℝ) *
        (hughesYoungReducedRight h k : ℝ) *
          (hughesYoungEpsilonRadius delta T : ℝ)) ≤
            162 * T ^ (7 : ℝ) := by
    calc
      _ ≤ ((3 * T) ^ 2) * ((3 * T) ^ 2) * (2 * T ^ (3 : ℝ)) := by
        gcongr
        · exact ha.trans hh'
        · exact hb.trans hk'
      _ = 162 * T ^ (7 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  simp only [Nat.cast_mul]
  exact hraw.trans
    ((oneHundredSixtyTwo_mul_rpow_seven_le_rpow_thirty hT).trans
      (rpow_thirty_le_globalDepth hT1))

set_option maxRecDepth 100000 in
/-- The opening-line tail is `O(T)` once the source truncation exponent and
the chosen AFE integration order satisfy the displayed quantitative
inequality.  This is the variable-parameter form of the fixed
`q = 1000`, `delta = .01` calculation. -/
theorem exists_norm_hughesYoungEpsilonOpeningRemainder_le_height
    (delta : ℝ) (q : ℕ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hq : 0 < q) (habsorb : (18 : ℝ) ≤ (2 * (q : ℝ) - 1) * delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ‖hughesYoungActiveWholeSmoothedRemainder q T
          (hughesYoungEpsilonRadius delta T) (hughesYoungGlobalDepth T)‖ ≤
        C * T := by
  obtain ⟨L, hL, hrem⟩ :=
    exists_norm_hughesYoungActiveWholeSmoothedRemainder_le
      q hq (1 / 2 : ℝ) (by norm_num) (by
        have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
        linarith)
  let C : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) *
      (256 * Real.exp (400 * (q : ℝ) ^ 2) *
        (7 + 2 * (q : ℝ)) ^ (4 * q + 8 : ℕ) *
        (hughesYoungReferenceDivisorPairMass (1 / 2) + 1) * L)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (by positivity))
      (mul_pos
        (mul_pos (mul_pos (by positivity) (by positivity))
          (by linarith [hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)])) hL)
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR := hughesYoungEpsilonRadius_pos (delta := delta) hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) *
            hughesYoungEpsilonRadius delta T : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungEpsilonRadius_cover hT2 hdelta0.le hdelta1 hh hk
  have hraw := hrem hT hR hcover
  have hraw' :
      ‖hughesYoungActiveWholeSmoothedRemainder q T
          (hughesYoungEpsilonRadius delta T) (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
            (((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8 : ℕ)) *
            (hughesYoungEpsilonRadius delta T : ℝ) ^
              (-(2 * (q : ℝ) - 1)) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) := by
    simpa only [show
        -(2 * (q : ℝ) - 1 / 2 - 1 / 2) =
            -(2 * (q : ℝ) - 1) by ring] using hraw
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hpair0 := hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)
  have hpair : hughesYoungReferenceDivisorPairMass (1 / 2) ≤
      hughesYoungReferenceDivisorPairMass (1 / 2) + 1 := by linarith
  have hqexp : 0 ≤ 2 * (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hrneg :
      (hughesYoungEpsilonRadius delta T : ℝ) ^
          (-(2 * (q : ℝ) - 1)) ≤
        T ^ (-(2 + delta) * (2 * (q : ℝ) - 1)) := by
    have hlower : T ^ (2 + delta) ≤
        (hughesYoungEpsilonRadius delta T : ℝ) :=
      hughesYoungEpsilonRadius_lower delta T
    have hneg := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hT0 (2 + delta)) hlower (neg_nonpos.mpr hqexp)
    calc
      _ ≤ (T ^ (2 + delta)) ^ (-(2 * (q : ℝ) - 1)) := hneg
      _ = T ^ (-(2 + delta) * (2 * (q : ℝ) - 1)) := by
        rw [← Real.rpow_mul hT0.le]
        congr 1
        ring
  let E : ℝ := 19 - (2 * (q : ℝ) - 1) * delta
  have hbound :
      (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
            (((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8 : ℕ)) *
            (hughesYoungEpsilonRadius delta T : ℝ) ^
              (-(2 * (q : ℝ) - 1)) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) ≤
        C * T ^ E := by
    calc
      _ ≤
          (15 * T / 4) * (81 * T ^ (4 : ℝ)) ^ 2 *
            (1 / Real.pi) *
            ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
              (((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8 : ℕ)) *
              T ^ (-(2 + delta) * (2 * (q : ℝ) - 1)) *
              (hughesYoungReferenceDivisorPairMass (1 / 2) + 1)) * L) := by
        gcongr
      _ = C * T ^ E := by
        have hfour : (T ^ (4 : ℝ)) ^ 2 = T ^ (8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num
        have hnat : T ^ (4 * q + 8 : ℕ) =
            T ^ ((4 * q + 8 : ℕ) : ℝ) :=
          (Real.rpow_natCast T (4 * q + 8)).symm
        have hpowers :
            T * T ^ (8 : ℝ) * T ^ (4 * q + 8 : ℕ) *
                T ^ (-(2 + delta) * (2 * (q : ℝ) - 1)) =
              T ^ E := by
          rw [hnat]
          calc
            _ = T ^ (1 : ℝ) * T ^ (8 : ℝ) *
                T ^ (((4 * q + 8 : ℕ) : ℝ)) *
                T ^ (-(2 + delta) * (2 * (q : ℝ) - 1)) := by
                  rw [Real.rpow_one]
            _ = T ^ E := by
              rw [← Real.rpow_add hT0, ← Real.rpow_add hT0,
                ← Real.rpow_add hT0]
              congr 1
              dsimp only [E]
              push_cast
              ring
        rw [mul_pow, hfour, mul_pow]
        calc
          _ = C * (T * T ^ (8 : ℝ) * T ^ (4 * q + 8 : ℕ) *
              T ^ (-(2 + delta) * (2 * (q : ℝ) - 1))) := by
            dsimp only [C]
            ring
          _ = C * T ^ E := by rw [hpowers]
  have hE : E ≤ 1 := by
    dsimp only [E]
    linarith
  have hpow : T ^ E ≤ T := by
    calc
      T ^ E ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 hE
      _ = T := Real.rpow_one T
  exact hraw'.trans <| hbound.trans <|
    mul_le_mul_of_nonneg_left hpow hC.le

theorem one_le_hughesYoungEpsilonSmoothingScale
    {delta T : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) :
    1 ≤ hughesYoungEpsilonSmoothingScale delta T := by
  have hp : 1 ≤ T ^ delta := Real.one_le_rpow hT hdelta
  unfold hughesYoungEpsilonSmoothingScale
  nlinarith

theorem hughesYoungEpsilonSmoothingScale_le_height
    {delta T : ℝ} (hT : 8 ≤ T) (hdelta1 : delta ≤ 1) :
    hughesYoungEpsilonSmoothingScale delta T ≤ T ^ 2 := by
  have hT1 : 1 ≤ T := by linarith
  have hp : T ^ delta ≤ T := by
    calc
      T ^ delta ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT1 hdelta1
      _ = T := Real.rpow_one T
  unfold hughesYoungEpsilonSmoothingScale
  nlinarith

/-- A source near-shift family is empty whenever even the first nonzero
integral frequency lies beyond the smoothing window.  This is the
parameter-free form of the half-unit cutoff used in the small-box branch. -/
theorem hughesYoungNearShifts_eq_empty_of_mul_lt
    {T P X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) (hPY : P * Y < T) :
    hughesYoungNearShifts T P X Y a b M N = ∅ := by
  classical
  ext r
  constructor
  · intro hr
    have hdata := (mem_hughesYoungNearShifts_iff.mp hr).2
    have hr0 : r ≠ 0 := hdata.1
    have hrOne : (1 : ℝ) ≤ |(r : ℝ)| := by
      have hint : (1 : ℤ) ≤ |r| := Int.one_le_abs hr0
      exact_mod_cast hint
    have hdiv : 1 / Y ≤ |(r : ℝ)| / Y :=
      div_le_div_of_nonneg_right hrOne hY.le
    have hmul : T * (1 / Y) ≤ T * (|(r : ℝ)| / Y) :=
      mul_le_mul_of_nonneg_left hdiv hT.le
    have hnear : T * (|(r : ℝ)| / Y) ≤ P := hdata.2.2.1
    have hstrict : P < T * (1 / Y) := by
      calc
        P < T / Y := (lt_div_iff₀ hY).2 hPY
        _ = T * (1 / Y) := by ring
    exfalso
    linarith
  · intro hr
    simp at hr

/-- The DFI equation-(27) series is zero when its source weight vanishes
on the translated diagonal.  This elementary form is useful when the two
dyadic supports are separated, rather than when the shift alone exceeds a
single support endpoint. -/
theorem dfiEquation27CentralSeries_eq_zero_of_shiftLine
    {f : ℝ → ℝ → ℂ} {a b h : ℕ}
    (hzero : ∀ x : ℝ, f x (x - h) = 0) :
    dfiEquation27CentralSeries a b h f = 0 := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand, dfiEquation27CentralIntegral,
    dfiEquation27C, hzero]
  simp

/-- If the right dyadic support is more than four times the left one, the
complete DFI central term vanishes on every Hughes--Young near shift. -/
theorem dfiSignedCentralSeries_reducedCleaned_eq_zero_of_right_separated
    {T c u P X Y : ℝ} {h k a b M N : ℕ} {r : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hXY : 4 * X < Y)
    (hr : r ∈ hughesYoungNearShifts T P X Y a b M N) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) = 0 := by
  have hdata := (mem_hughesYoungNearShifts_iff.mp hr).2
  have hr0 : r ≠ 0 := hdata.1
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        apply hr0
        simp [Nat.eq_zero_of_not_pos hn0]
      change dfiSignedCentralSeries a b (n : ℤ)
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (n : ℤ)) = 0
      rw [dfiSignedCentralSeries_ofNat]
      apply dfiEquation27CentralSeries_eq_zero_of_shiftLine
      intro x
      by_contra hne
      have hs : (x, x - (n : ℝ)) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        (hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale
          (T := T) (c := c) (u := u) hX hY h k (n : ℤ)).support_subset hne
      have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hyx : x - (n : ℝ) ≤ x := by linarith
      linarith [hs.1.2, hs.2.1]
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hrEq : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hrEq, dfiSignedCentralSeries_neg_ofNat a b m hm]
      apply dfiEquation27CentralSeries_eq_zero_of_shiftLine
      intro y
      by_contra hne
      have hs : (y - (m : ℝ), y) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
        apply (hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale
          (T := T) (c := c) (u := u) hX hY h k (-(m : ℤ))).support_subset
        exact hne
      have hrNear : (m : ℝ) ≤ Y / 2 := by
        have habs := hdata.2.1
        rw [hrEq] at habs
        rw [Int.cast_neg, Int.cast_natCast, abs_neg] at habs
        have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        rw [abs_of_nonneg hmNonneg] at habs
        exact habs
      have hgap : Y / 2 < Y - 2 * X := by linarith
      have hmGap : Y - 2 * X ≤ (m : ℝ) := by
        change (y - (m : ℝ), y) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) at hs
        linarith [hs.1.2, hs.2.1]
      linarith

/-- Symmetric separated-support vanishing when the left dyadic support is
more than four times the right one. -/
theorem dfiSignedCentralSeries_reducedCleaned_eq_zero_of_left_separated
    {T c u P X Y : ℝ} {h k a b M N : ℕ} {r : ℤ}
    (hX : 0 < X) (hY : 0 < Y) (hYX : 4 * Y < X)
    (hr : r ∈ hughesYoungNearShifts T P X Y a b M N) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) = 0 := by
  have hdata := (mem_hughesYoungNearShifts_iff.mp hr).2
  have hr0 : r ≠ 0 := hdata.1
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hn0
        apply hr0
        simp [Nat.eq_zero_of_not_pos hn0]
      change dfiSignedCentralSeries a b (n : ℤ)
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (n : ℤ)) = 0
      rw [dfiSignedCentralSeries_ofNat]
      apply dfiEquation27CentralSeries_eq_zero_of_shiftLine
      intro x
      by_contra hne
      have hs : (x, x - (n : ℝ)) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        (hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale
          (T := T) (c := c) (u := u) hX hY h k (n : ℤ)).support_subset hne
      have hrNear : (n : ℝ) ≤ Y / 2 := by
        have habs := hdata.2.1
        have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        convert habs using 1
        norm_num [abs_of_nonneg hnNonneg]
      have hnGap : X - 2 * Y ≤ (n : ℝ) := by
        change (x, x - (n : ℝ)) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) at hs
        linarith [hs.1.1, hs.2.2]
      linarith
  | negSucc n =>
      let m : ℕ := n + 1
      have hm : 0 < m := by omega
      have hrEq : Int.negSucc n = -(m : ℤ) := by
        dsimp only [m]
        omega
      rw [hrEq, dfiSignedCentralSeries_neg_ofNat a b m hm]
      apply dfiEquation27CentralSeries_eq_zero_of_shiftLine
      intro y
      by_contra hne
      have hs : (y - (m : ℝ), y) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
        apply (hughesYoungReducedCleanedShiftWeight_localizedBox_positiveScale
          (T := T) (c := c) (u := u) hX hY h k (-(m : ℤ))).support_subset
        exact hne
      have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith [hs.1.1, hs.2.2]

/-- An empty source near-window kills the integrated signed central box
definitionally. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_nearShifts_empty
    {T c H P X Y : ℝ} {h k M N : ℕ}
    (hempty : hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N = ∅) :
    hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N = 0 := by
  unfold hughesYoungNearPointwiseSignedCentralBox
    hughesYoungIntegratedPointwiseSignedCentral
  rw [hempty]
  simp

/-- The integrated near central box vanishes when its right dyadic support
is more than four times the left support. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_right_separated
    {T c H P X Y : ℝ} {h k M N : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hXY : 4 * X < Y) :
    hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N = 0 := by
  unfold hughesYoungNearPointwiseSignedCentralBox
    hughesYoungIntegratedPointwiseSignedCentral
  calc
    _ = ∫ _u : ℝ in -H..H, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro r hr
      exact dfiSignedCentralSeries_reducedCleaned_eq_zero_of_right_separated
        hX hY hXY hr
    _ = 0 := intervalIntegral.integral_zero

/-- Symmetric integrated vanishing when the left dyadic support is more
than four times the right support. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_left_separated
    {T c H P X Y : ℝ} {h k M N : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hYX : 4 * Y < X) :
    hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N = 0 := by
  unfold hughesYoungNearPointwiseSignedCentralBox
    hughesYoungIntegratedPointwiseSignedCentral
  calc
    _ = ∫ _u : ℝ in -H..H, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro r hr
      exact dfiSignedCentralSeries_reducedCleaned_eq_zero_of_left_separated
        hX hY hYX hr
    _ = 0 := intervalIntegral.integral_zero

/-- At the native Hughes--Young smoothing scale, the square of the
smoothing parameter is eventually smaller than the physical height by the
precise margin needed to empty every comparable non-large near window. -/
theorem eventually_threeHundredTwenty_mul_hughesYoungDFISmoothingScale_sq_lt :
    ∀ᶠ T : ℝ in atTop,
      320 * hughesYoungDFISmoothingScale T *
          hughesYoungDFISmoothingScale T < T := by
  have hgrow : Tendsto (fun T : ℝ => T ^ (4999 / 5000 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      hgrow.eventually (eventually_gt_atTop (20480 : ℝ))] with T hT hpow
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hfactor :
      320 * hughesYoungDFISmoothingScale T *
          hughesYoungDFISmoothingScale T =
        20480 * T ^ (1 / 5000 : ℝ) := by
    unfold hughesYoungDFISmoothingScale
    calc
      320 * (8 * T ^ (1 / 10000 : ℝ)) *
          (8 * T ^ (1 / 10000 : ℝ)) =
        20480 * (T ^ (1 / 10000 : ℝ) *
          T ^ (1 / 10000 : ℝ)) := by ring
      _ = 20480 * T ^ (1 / 5000 : ℝ) := by
        rw [← Real.rpow_add hT0]
        norm_num
  calc
    320 * hughesYoungDFISmoothingScale T *
          hughesYoungDFISmoothingScale T =
        20480 * T ^ (1 / 5000 : ℝ) := hfactor
    _ < T ^ (4999 / 5000 : ℝ) * T ^ (1 / 5000 : ℝ) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hT0 _)
    _ = T := by
      rw [← Real.rpow_add hT0, ← Real.rpow_one T]
      norm_num

/-- A small comparable physical scale has no retained integral shift at
the native smoothing parameter once the global height is large enough. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_native_smallScale
    {T c H X Y : ℝ} {h k M N : ℕ}
    (hT : 0 < T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hY : 0 < Y)
    (hYsmall : Y < 320 * hughesYoungDFISmoothingScale T) :
    hughesYoungNearPointwiseSignedCentralBox T c H
        (hughesYoungDFISmoothingScale T) X Y h k M N = 0 := by
  have hP0 : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  apply hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_nearShifts_empty
  apply hughesYoungNearShifts_eq_empty_of_mul_lt hT hY
  calc
    hughesYoungDFISmoothingScale T * Y <
        hughesYoungDFISmoothingScale T *
          (320 * hughesYoungDFISmoothingScale T) :=
      mul_lt_mul_of_pos_left hYsmall hP0
    _ = 320 * hughesYoungDFISmoothingScale T *
          hughesYoungDFISmoothingScale T := by ring
    _ < T := hsmall

/-- Source-order exhaustion of the regular complement of the DFI range.
The two endpoint cases have already been removed by
`hughesYoungCentralRegularBoxes`, so the only remaining failures are the
two arithmetic-support inequalities, the optimized-scale inequality, and
the two comparability inequalities. -/
theorem hughesYoungCentralRegularNonLargeBoxes_cases
    {P : ℝ} {a b R K : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes P a b R K) :
    ¬ (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∨
      ¬ (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2 ∨
      hughesYoungDFIOptimalU P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) < 64 ∨
      4 * hughesYoungFullDyadicScale ij.2 <
          hughesYoungFullDyadicScale ij.1 ∨
      4 * hughesYoungFullDyadicScale ij.1 <
          hughesYoungFullDyadicScale ij.2 := by
  have hnot := (Finset.mem_filter.mp hij).2
  by_cases ha : (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1
  · by_cases hb : (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2
    · by_cases hU : 64 ≤ hughesYoungDFIOptimalU P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2)
      · by_cases hXY : hughesYoungFullDyadicScale ij.1 ≤
            4 * hughesYoungFullDyadicScale ij.2
        · by_cases hYX : hughesYoungFullDyadicScale ij.2 ≤
              4 * hughesYoungFullDyadicScale ij.1
          · exact False.elim (hnot ⟨ha, hb, hU, hXY, hYX⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (lt_of_not_ge hYX))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (lt_of_not_ge hXY))))
      · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge hU)))
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

/-- On a source-supported regular box outside the optimized DFI range, the
retained near central family vanishes at the native smoothing scale.  The
proof follows the source alternatives in Hughes--Young (65)--(69): a
noncomparable box has disjoint dyadic supports, while a comparable box with
small optimized scale has an empty nonzero-shift window. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_regularNonLarge
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 0 < T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes
      (hughesYoungDFISmoothingScale T)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (haX : (hughesYoungReducedLeft h k : ℝ) ≤
      2 * hughesYoungFullDyadicScale ij.1)
    (hbY : (hughesYoungReducedRight h k : ℝ) ≤
      2 * hughesYoungFullDyadicScale ij.2) :
    hughesYoungNearPointwiseSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungDFISmoothingScale T)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) = 0 := by
  have hregular := (Finset.mem_filter.mp hij).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hi : 0 < ij.1 := hpos.1
  have hj : 0 < ij.2 := hpos.2
  have hX : 0 < hughesYoungFullDyadicScale ij.1 :=
    hughesYoungFullDyadicScale_pos ij.1
  have hY : 0 < hughesYoungFullDyadicScale ij.2 :=
    hughesYoungFullDyadicScale_pos ij.2
  by_cases hleft :
      4 * hughesYoungFullDyadicScale ij.2 <
        hughesYoungFullDyadicScale ij.1
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_left_separated
      hX hY hleft
  by_cases hright :
      4 * hughesYoungFullDyadicScale ij.1 <
        hughesYoungFullDyadicScale ij.2
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_right_separated
      hX hY hright
  have hcases := hughesYoungCentralRegularNonLargeBoxes_cases hij
  have hU : hughesYoungDFIOptimalU (hughesYoungDFISmoothingScale T)
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) < 64 := by
    rcases hcases with hbadA | hbadB | hU | hleft' | hright'
    · exact False.elim (hbadA haX)
    · exact False.elim (hbadB hbY)
    · exact hU
    · exact False.elim (hleft hleft')
    · exact False.elim (hright hright')
  have hP : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  have hYsmall : hughesYoungFullDyadicScale ij.2 <
      320 * hughesYoungDFISmoothingScale T :=
    hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
      hP hX hY (le_of_not_gt hright) hU
  exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_native_smallScale
    hT hsmall hY hYsmall

/-- Equation (81) on one supported regular complementary box: after the
near family vanishes, the complete signed central source is exactly its
equation-(65) far-shift extension. -/
theorem hughesYoungIntegratedCompleteCentral_eq_far_of_regularNonLarge
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hh : 0 < h) (hk : 0 < k)
    (hij : ij ∈ hughesYoungCentralRegularNonLargeBoxes
      (hughesYoungDFISmoothingScale T)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (haX : (hughesYoungReducedLeft h k : ℝ) ≤
      2 * hughesYoungFullDyadicScale ij.1)
    (hbY : (hughesYoungReducedRight h k : ℝ) ≤
      2 * hughesYoungFullDyadicScale ij.2) :
    hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) =
      hughesYoungIntegratedPointwiseSignedCentral T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFarShifts T (hughesYoungDFISmoothingScale T)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)) := by
  have hregular := (Finset.mem_filter.mp hij).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.1.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ j
  have hc := hughesYoungSmallContour_spec
    (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ T))
  let U : ℝ := (hughesYoungDFISmoothingScale T)⁻¹ *
    min (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have hEq := hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    (T := T) (c := hughesYoungSmallContour T) (H := T / 8)
    (P := hughesYoungDFISmoothingScale T) (U := U)
    (X := hughesYoungFullDyadicScale ij.1)
    (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
    (M := hughesYoungFullDyadicBound ij.1)
    (N := hughesYoungFullDyadicBound ij.2)
    hT hc.1 hc.2.1 (by positivity) le_rfl (lt_of_lt_of_le zero_lt_one hP)
    hPT hX hY hh hk hP hU le_rfl
  rw [hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_regularNonLarge
    (lt_of_lt_of_le (by norm_num) hT) hsmall hij haX hbY] at hEq
  exact sub_eq_zero.mp hEq.symm

/-- The regular non-large boxes on which the literal positive-coordinate
source support is present.  The omitted regular boxes are the two
support-failure families and are deliberately left for the telescoping
endpoint reassembly. -/
noncomputable def hughesYoungSupportedRegularNonLargeBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungCentralRegularNonLargeBoxes P a b R K).filter fun ij =>
    (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
      (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2

/-- The source-valid part of the active rectangle: both dyadic indices are
ordinary positive scales and both reduced arithmetic lattices meet the
corresponding real support boxes.  This is the exact family on which the
large-DFI and supported non-large central terms partition the source. -/
noncomputable def hughesYoungActiveRegularSupportedBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter fun ij =>
    0 < ij.1 ∧ 0 < ij.2 ∧
      (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
      (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2

/-- The complete finite dyadic rectangle restricted only by the genuine
positive-scale and arithmetic-support conditions.  Unlike the active
family, it has no physical product cutoff. -/
noncomputable def hughesYoungRectangularRegularSupportedBoxes
    (a b K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungCompleteDyadicRectangle K).filter fun ij =>
    0 < ij.1 ∧ 0 < ij.2 ∧
      (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
      (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2

/-- Source-valid ordinary boxes beyond the physical AFE product cutoff. -/
noncomputable def hughesYoungInactiveRegularSupportedBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungRectangularRegularSupportedBoxes a b K).filter fun ij =>
    ¬ (hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))

/-- Exact index identity behind the source-faithful version of
Hughes--Young (82): the active, positive, support-valid boxes are precisely
the disjoint union of the optimized DFI boxes and their supported regular
complement. -/
theorem hughesYoungActiveRegularSupportedBoxes_eq_large_union_nonLarge
    (P : ℝ) (a b R K : ℕ) :
    hughesYoungActiveRegularSupportedBoxes a b R K =
      hughesYoungActiveLargeDFIBoxes P a b R K ∪
        hughesYoungSupportedRegularNonLargeBoxes P a b R K := by
  classical
  ext ij
  simp only [hughesYoungActiveRegularSupportedBoxes,
    hughesYoungActiveLargeDFIBoxes,
    hughesYoungSupportedRegularNonLargeBoxes,
    hughesYoungCentralRegularNonLargeBoxes,
    hughesYoungCentralRegularBoxes, Finset.mem_union, Finset.mem_filter]
  by_cases hU : 64 ≤ hughesYoungDFIOptimalU P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
  · by_cases hXY : hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2
    · by_cases hYX : hughesYoungFullDyadicScale ij.2 ≤
          4 * hughesYoungFullDyadicScale ij.1 <;>
        simp [hU, hXY, hYX, and_assoc]
    · simp [hU, hXY, and_assoc]
  · simp [hU, and_assoc]

/-- The two families in the preceding exact union are disjoint. -/
theorem disjoint_hughesYoungActiveLargeDFIBoxes_supportedRegularNonLarge
    (P : ℝ) (a b R K : ℕ) :
    Disjoint (hughesYoungActiveLargeDFIBoxes P a b R K)
      (hughesYoungSupportedRegularNonLargeBoxes P a b R K) := by
  classical
  rw [Finset.disjoint_left]
  intro ij hlarge hsmall
  have hlarge' := (Finset.mem_filter.mp hlarge).2
  have hsmall' := (Finset.mem_filter.mp hsmall).1
  exact (Finset.mem_filter.mp hsmall').2 hlarge'.2.2

/-- Exact active/inactive split inside the positive support-valid finite
rectangle. -/
theorem hughesYoungRectangularRegularSupportedBoxes_eq_active_union_inactive
    (a b R K : ℕ) :
    hughesYoungRectangularRegularSupportedBoxes a b K =
      hughesYoungActiveRegularSupportedBoxes a b R K ∪
        hughesYoungInactiveRegularSupportedBoxes a b R K := by
  classical
  ext ij
  simp only [hughesYoungRectangularRegularSupportedBoxes,
    hughesYoungActiveRegularSupportedBoxes,
    hughesYoungInactiveRegularSupportedBoxes,
    hughesYoungActiveDyadicBoxes, hughesYoungCompleteDyadicRectangle,
    Finset.mem_union, Finset.mem_filter, Nat.cast_mul]
  by_cases hactive : hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤
        (a : ℝ) * (b : ℝ) * (R : ℝ)
  · simp [hactive, and_assoc]
  · have hinactive : (a : ℝ) * (b : ℝ) * (R : ℝ) <
        hughesYoungFullDyadicScale ij.1 *
          hughesYoungFullDyadicScale ij.2 := lt_of_not_ge hactive
    simp [hactive, and_assoc]

/-- The active and inactive support-valid families are disjoint. -/
theorem disjoint_hughesYoungActiveRegularSupportedBoxes_inactive
    (a b R K : ℕ) :
    Disjoint (hughesYoungActiveRegularSupportedBoxes a b R K)
      (hughesYoungInactiveRegularSupportedBoxes a b R K) := by
  classical
  rw [Finset.disjoint_left]
  intro ij hactive hinactive
  have hp := (Finset.mem_filter.mp hactive).1
  have hproduct := (Finset.mem_filter.mp hp).2
  exact (Finset.mem_filter.mp hinactive).2 hproduct

/-- Complete central source over the supported regular complement. -/
noncomputable def hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete central source over all active, positive-coordinate,
support-valid boxes. -/
noncomputable def hughesYoungActiveRegularSupportedIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveRegularSupportedBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete central source over the positive-coordinate,
support-valid part of the entire finite dyadic rectangle. -/
noncomputable def hughesYoungRectangularRegularSupportedIntegratedCompleteCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungRectangularRegularSupportedBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete central source over support-valid ordinary boxes outside
the physical AFE product cutoff. -/
noncomputable def hughesYoungInactiveRegularSupportedIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveRegularSupportedBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Aggregate form of the exact active source partition. -/
theorem hughesYoungActiveRegularSupportedIntegratedCompleteCentral_eq_large_add_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveRegularSupportedIntegratedCompleteCentral T R K =
      hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K +
        hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T P R K := by
  classical
  unfold hughesYoungActiveRegularSupportedIntegratedCompleteCentral
    hughesYoungActiveLargeDFIIntegratedCompleteCentral
    hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hughesYoungActiveRegularSupportedBoxes_eq_large_union_nonLarge,
    Finset.sum_union
      (disjoint_hughesYoungActiveLargeDFIBoxes_supportedRegularNonLarge
        P (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)]

/-- Aggregate form of the exact active/inactive source partition. -/
theorem hughesYoungRectangularRegularSupportedIntegratedCompleteCentral_eq_active_add_inactive
    (T : ℝ) (R K : ℕ) :
    hughesYoungRectangularRegularSupportedIntegratedCompleteCentral T K =
      hughesYoungActiveRegularSupportedIntegratedCompleteCentral T R K +
        hughesYoungInactiveRegularSupportedIntegratedCompleteCentral T R K := by
  classical
  unfold hughesYoungRectangularRegularSupportedIntegratedCompleteCentral
    hughesYoungActiveRegularSupportedIntegratedCompleteCentral
    hughesYoungInactiveRegularSupportedIntegratedCompleteCentral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hughesYoungRectangularRegularSupportedBoxes_eq_active_union_inactive,
    Finset.sum_union
      (disjoint_hughesYoungActiveRegularSupportedBoxes_inactive
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)]

/-- Equation-(65) far central family over the same supported regular
complement. -/
noncomputable def hughesYoungSupportedRegularNonLargeIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
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

/-- Finite-sum equation-(81) extension for every supported regular box in
the non-large complement. -/
theorem hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral_eq_tail
    {T : ℝ} (hT : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (R K : ℕ) :
    hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) R K =
      hughesYoungSupportedRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) R K := by
  classical
  unfold hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral
    hughesYoungSupportedRegularNonLargeIntegratedCentralTail
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := (Finset.mem_filter.mp hij).2
  exact hughesYoungIntegratedCompleteCentral_eq_far_of_regularNonLarge
    hT hP hPT hsmall
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1)
    (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1)
    (Finset.mem_filter.mp hij).1 hs.1 hs.2

/-- The global polynomial equation-(65) envelope also applies to a
supported regular complementary box.  Only active-rectangle membership and
positive dyadic indices enter this estimate; the large-DFI predicate is
irrelevant once the near family has vanished. -/
theorem hughesYoungFarSignedCentralStaticMass_le_supportedRegularEnvelope
    {T P : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : Real.exp 1 ≤ T)
    (hhmem : h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hkmem : k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2))
    (hij : ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
        (hughesYoungFullDyadicScale ij.1) (hughesYoungFullDyadicScale ij.2)
        h k (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) ≤
      3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
        hughesYoungCentralTailSeriesConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
        (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ) := by
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hc := hughesYoungSmallContour_spec hT
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hhle : h ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hhmem).2
  have hkle : k ≤ ell := by simpa only [ell] using (Finset.mem_Icc.mp hkmem).2
  have ha : 0 < hughesYoungReducedLeft h k := hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k := hughesYoungReducedRight_pos hh hk
  have haell : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hhle
  have hbell : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hkle
  have hnonLarge := (Finset.mem_filter.mp hij).1
  have hregular := (Finset.mem_filter.mp hnonLarge).1
  have hactive := (Finset.mem_filter.mp hregular).1
  have hpos := (Finset.mem_filter.mp hregular).2
  have hi : 0 < ij.1 := hpos.1
  have hj : 0 < ij.2 := hpos.2
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
  have hMnat : hughesYoungFullDyadicBound ij.1 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_left
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hNnat : hughesYoungFullDyadicBound ij.2 ≤ B := by
    have hraw := hughesYoungFullDyadicBound_le_four_mul_activeConductor_add_one_right
      hactive
    have hprod : hughesYoungReducedLeft h k * hughesYoungReducedRight h k * R ≤
        ell * ell * R := Nat.mul_le_mul_right R (Nat.mul_le_mul haell hbell)
    unfold B hughesYoungActiveArithmeticCutoff
    exact hraw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hprod) 1)
  have hXB : hughesYoungFullDyadicScale ij.1 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.1
    exact (by linarith : hughesYoungFullDyadicScale ij.1 ≤
      (hughesYoungFullDyadicBound ij.1 : ℝ)).trans (by exact_mod_cast hMnat)
  have hYB : hughesYoungFullDyadicScale ij.2 ≤ (B : ℝ) := by
    have htwo := two_mul_hughesYoungFullDyadicScale_le_bound ij.2
    exact (by linarith : hughesYoungFullDyadicScale ij.2 ≤
      (hughesYoungFullDyadicBound ij.2 : ℝ)).trans (by exact_mod_cast hNnat)
  have hell1 : 1 ≤ ell := by
    have hcut : 0 < detectorCutoff T := by unfold detectorCutoff; omega
    simpa only [ell] using Nat.one_le_pow 2 (detectorCutoff T) hcut
  have hB1 : 1 ≤ B := by unfold B hughesYoungActiveArithmeticCutoff; omega
  have hR : 0 < R := by
    have hprod := (Finset.mem_filter.mp hactive).2
    have hprodPos : 0 < hughesYoungFullDyadicScale ij.1 *
        hughesYoungFullDyadicScale ij.2 := mul_pos
      (hughesYoungFullDyadicScale_pos ij.1) (hughesYoungFullDyadicScale_pos ij.2)
    have hcastPos : 0 < ((hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R : ℕ) : ℝ) := hprodPos.trans_le hprod
    have hnatPos : 0 < hughesYoungReducedLeft h k *
        hughesYoungReducedRight h k * R := by exact_mod_cast hcastPos
    exact pos_of_mul_pos_right hnatPos (Nat.zero_le _)
  have hellB : ell ≤ B := by
    unfold B hughesYoungActiveArithmeticCutoff
    change ell ≤ 4 * (ell * ell * R) + 1
    have hsquare : ell ≤ ell * ell := Nat.le_mul_of_pos_right ell hell1
    have hRmul : ell * ell ≤ ell * ell * R :=
      Nat.le_mul_of_pos_right (ell * ell) hR
    exact hsquare.trans (hRmul.trans (by omega))
  simpa only [ell, B] using hughesYoungFarSignedCentralStaticMass_le_polynomial
    hT1 hc.1.le hc.2.1 hX hY (by exact_mod_cast hell1) (by exact_mod_cast hB1)
    hh hk ha hb (by exact_mod_cast hhle) (by exact_mod_cast hkle)
    (by exact_mod_cast haell) (by exact_mod_cast hbell) (by exact_mod_cast hellB)
    hXB hYB (by exact_mod_cast hMnat) (by exact_mod_cast hNnat)

/-- Equation-(65) decay summed over the supported regular non-large
complement.  This is the same quantitative tail calculation as for the
large-DFI family, but with the exact source complement as its index set. -/
theorem exists_scaled_norm_hughesYoungSupportedRegularNonLargeIntegratedCentralTail_le
    (j : ℕ) :
    ∃ Cγ L : ℝ, 0 < Cγ ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungSupportedRegularNonLargeIntegratedCentralTail T P R K‖ ≤
        (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) *
        hughesYoungCentralTailPolynomialEnvelope Cw L j T
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
          (hughesYoungActiveArithmeticCutoff T R : ℝ) := by
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hlocal⟩ :=
    exists_norm_hughesYoungIntegratedFarSignedCentral_full_bound j
  refine ⟨Cγ, L, hCγ, hL, Cw, hCw, ?_⟩
  intro T P R K hT hT16 hP hPT hcontour
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let A : ℝ := (P / (5 * T)) ^ j
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L j T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T R : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hc := hughesYoungSmallContour_spec hT
  have hbox : ∀ h ∈ S, ∀ k ∈ S,
      ∀ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      A * ‖hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))‖ ≤ E := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hnonLarge := (Finset.mem_filter.mp hij).1
    have hregular := (Finset.mem_filter.mp hnonLarge).1
    have hpos := (Finset.mem_filter.mp hregular).2
    have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.1.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using
        one_le_hughesYoungFullDyadicScale_succ i
    have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
      obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hpos.2.ne'
      rw [hiEq]
      simpa only [Nat.succ_eq_add_one] using
        one_le_hughesYoungFullDyadicScale_succ i
    have hraw := hlocal (T := T) (c := hughesYoungSmallContour T)
      (H := T / 8) (P := P)
      (X := hughesYoungFullDyadicScale ij.1)
      (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
      (M := hughesYoungFullDyadicBound ij.1)
      (N := hughesYoungFullDyadicBound ij.2)
      hT16 hc.1 hc.2.1 hcontour (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT (by linarith) (by linarith) hh hk
    have hmass := hughesYoungFarSignedCentralStaticMass_le_supportedRegularEnvelope
      hT hhmem hkmem hij
    have hfactor : 0 ≤ T *
        hughesYoungFarSignedCentralStaticMass T (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) :=
      mul_nonneg (by positivity) (hughesYoungFarSignedCentralStaticMass_nonneg
        (by positivity) (zero_le_one.trans hX) (zero_le_one.trans hY) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2))
    have hanalytic : 0 ≤ (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ *
        Real.exp 100 * (6 * T) *
        hughesYoungHeightInputDerivativeConstant Cw j * ((T / 16)⁻¹) ^ j) * L) := by
      have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw j
      have hsmallInv : 0 ≤ (hughesYoungSmallContour T)⁻¹ := inv_nonneg.mpr hc.1.le
      positivity
    calc
      _ ≤ T * hughesYoungFarSignedCentralStaticMass T
          (hughesYoungSmallContour T) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1) (hughesYoungFullDyadicBound ij.2) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by simpa only [A] using hraw
      _ ≤ T * (3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
          hughesYoungCentralTailSeriesConstant *
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ)) ^ (11 : ℕ) *
          (hughesYoungActiveArithmeticCutoff T R : ℝ) ^ (6 : ℕ)) *
        (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
          (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
          ((T / 16)⁻¹) ^ j) * L) := by gcongr
      _ = E := by rfl
  unfold hughesYoungSupportedRegularNonLargeIntegratedCentralTail
  change A * ‖∑ h ∈ S, ∑ k ∈ S,
      ∑ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
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
            (hughesYoungFullDyadicBound ij.2))‖ ≤ _
  calc
    _ ≤ A * ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by
      exact mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
            norm_sum_le _ _))) hA
    _ = ∑ h ∈ S, ∑ k ∈ S,
        ∑ ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          A * ‖hughesYoungIntegratedPointwiseSignedCentral T
            (hughesYoungSmallContour T) (T / 8)
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2) h k
            (hughesYoungFarShifts T P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2))‖ := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ _h ∈ S, ∑ _k ∈ S, (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      calc
        _ ≤ ∑ _ij ∈ hughesYoungSupportedRegularNonLargeBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            E := Finset.sum_le_sum (hbox h hhmem k hkmem)
        _ = ((hughesYoungSupportedRegularNonLargeBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) * E := by simp
        _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast (calc
            (hughesYoungSupportedRegularNonLargeBoxes P
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card ≤
              (hughesYoungActiveDyadicBoxes
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card := by
                  apply Finset.card_le_card
                  intro ij hij
                  exact (Finset.mem_filter.mp
                    (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1).1
            _ ≤ (K + 2) ^ 2 := card_hughesYoungActiveDyadicBoxes_le _ _ _ _)
    _ = (S.card : ℝ) ^ 2 * (((K + 2 : ℕ) : ℝ) ^ 2) * E := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
          (((K + 2 : ℕ) : ℝ) ^ 2)) * E := by
      have hcardNat : S.card ≤ (detectorCutoff T) ^ 2 := by simp [S]
      have hcard : (S.card : ℝ) ≤ (((detectorCutoff T) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      gcongr
    _ = _ := by rfl

/-- The supported regular complementary central family is negligible at
the conductor radius.  This consumes the source-level near-zero identity
and the uniform equation-(65) far-tail estimate. -/
theorem hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨Cγ, L, hCγ, hL, Cw, hCw, hscaled⟩ :=
    exists_scaled_norm_hughesYoungSupportedRegularNonLargeIntegratedCentralTail_le
      4000000
  let C : ℝ := 3 * (15 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungCentralTailSeriesConstant * 9 ^ 11 * 649 ^ 6 *
    (15 / 4) * Real.exp 100 * 6 *
    hughesYoungHeightInputDerivativeConstant Cw 4000000 * L
  let A : ℝ := 81 * 103 ^ 2 * C
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hheight := hughesYoungHeightInputDerivativeConstant_pos hCw 4000000
    exact mul_nonneg
      (mul_nonneg hughesYoungCentralTailNumericalConstant_nonneg hheight.le) hL.le
  have hA : 0 ≤ A := by dsimp only [A]; exact mul_nonneg (by norm_num) hC
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungNativeNonLargeDecayBases,
      eventually_hughesYoungDFISmoothingScale_native_range,
      eventually_four_mul_hughesYoungSmallContour_le_one hCγ,
      eventually_threeHundredTwenty_mul_hughesYoungDFISmoothingScale_sq_lt,
      eventually_ge_atTop (16 : ℝ)] with T hBases hRange hContour hSmall hT16
  have hT : Real.exp 1 ≤ T := hBases.1
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hP0 : 0 < hughesYoungDFISmoothingScale T :=
    zero_lt_one.trans_le hRange.2.1
  let Q : ℝ := (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 *
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2
  let E : ℝ := hughesYoungCentralTailPolynomialEnvelope Cw L 4000000 T
    ((((detectorCutoff T) ^ 2 : ℕ) : ℝ))
    (hughesYoungActiveArithmeticCutoff T (hughesYoungConductorRadius T) : ℝ)
  let B : ℝ := (hughesYoungDFISmoothingScale T / (5 * T)) ^ (4000000 : ℕ)
  let F : ℝ := (5 * T / hughesYoungDFISmoothingScale T) ^ (4000000 : ℕ)
  have hB : 0 < B := by dsimp only [B]; exact pow_pos (div_pos hP0 (by positivity)) _
  have hBF : B * F = 1 := by
    dsimp only [B, F]
    rw [← mul_pow]
    have hbase : hughesYoungDFISmoothingScale T / (5 * T) *
        (5 * T / hughesYoungDFISmoothingScale T) = 1 := by
      field_simp [ne_of_gt hP0, ne_of_gt hT0]
    rw [hbase, one_pow]
  have hRaw := hscaled (T := T) (P := hughesYoungDFISmoothingScale T)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT hT16 hRange.2.1 hRange.2.2 hContour.2
  have hUnscaled :
      ‖hughesYoungSupportedRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ Q * (F * E) := by
    have hMultiplied : B *
        ‖hughesYoungSupportedRegularNonLargeIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
          (hughesYoungGlobalDepth T)‖ ≤ B * (Q * (F * E)) := by
      calc
        _ ≤ Q * E := by simpa only [B, Q, E] using hRaw
        _ = B * (Q * (F * E)) := by
          calc
            Q * E = (B * F) * (Q * E) := by rw [hBF, one_mul]
            _ = B * (Q * (F * E)) := by ac_rfl
    exact le_of_mul_le_mul_left hMultiplied hB
  have hEnvelope : F * E ≤ C * T ^ (-32 : ℝ) := by
    simpa only [F, E, C] using
      hughesYoungNativeCentralTailEnvelope_le_rpow_neg_thirty_two
        hT hL.le hCw hBases.2.2.2
  have hCut := detectorCutoff_sq_le_nine_mul_rpow_one_fiftieth hT1
  have hCutLoose : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) :=
    hCut.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) (by norm_num))
  have hCutSq : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) ≤
      81 * T ^ (4 : ℝ) := by
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) ^ 2 := by gcongr
      _ = 81 * T ^ (4 : ℝ) := by
        rw [mul_pow]
        rw [show (T ^ (2 : ℝ)) ^ 2 = T ^ (4 : ℝ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          norm_num]
        norm_num
  have hDepth := hughesYoungGlobalDepth_add_two_le_rpow
    (show (0 : ℝ) < 1 by norm_num) hT
  have hDepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      103 ^ 2 * T ^ (2 : ℝ) := by
    have hDepth' : ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
        103 * T ^ (1 : ℝ) := by
      norm_num at hDepth ⊢
      exact hDepth
    calc
      _ ≤ (103 * T ^ (1 : ℝ)) ^ 2 := by gcongr
      _ = 103 ^ 2 * T ^ (2 : ℝ) := by rw [Real.rpow_one, Real.rpow_two]; ring
  have hQ : Q ≤ 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
    dsimp only [Q]
    calc
      _ ≤ (81 * T ^ (4 : ℝ)) * (103 ^ 2 * T ^ (2 : ℝ)) := by gcongr
      _ = 81 * 103 ^ 2 * T ^ (6 : ℝ) := by
        rw [show T ^ (6 : ℝ) = T ^ (4 : ℝ) * T ^ (2 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact hughesYoungCentralTailPolynomialEnvelope_nonneg hT hL.le hCw
      (by positivity) (by positivity)
  have hFE0 : 0 ≤ F * E := mul_nonneg
    (by dsimp only [F]; exact pow_nonneg (div_nonneg (by positivity) hP0.le) _) hE0
  have hBound :
      ‖hughesYoungSupportedRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T)‖ ≤ A * T ^ (-26 : ℝ) := by
    calc
      _ ≤ Q * (F * E) := hUnscaled
      _ ≤ (81 * 103 ^ 2 * T ^ (6 : ℝ)) * (C * T ^ (-32 : ℝ)) :=
        mul_le_mul hQ hEnvelope hFE0 (by positivity)
      _ = A * T ^ (-26 : ℝ) := by
        dsimp only [A]
        rw [show T ^ (-26 : ℝ) = T ^ (6 : ℝ) * T ^ (-32 : ℝ) by
          rw [← Real.rpow_add hT0]
          norm_num]
        ring
  have hPow : T ^ (-26 : ℝ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral_eq_tail
    hT16 hRange.2.1 hRange.2.2 hSmall]
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungSupportedRegularNonLargeIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) (hughesYoungConductorRadius T)
        (hughesYoungGlobalDepth T))), hTarget]
  exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)

/-- The conductor-scale opening remainder is harmless in the native
`T^(1+epsilon)` fourth-moment estimate. -/
theorem hughesYoungConductorOpeningRemainder_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveWholeSmoothedRemainder 1000 T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungConductorOpeningRemainder_le_height
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hpow : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungActiveWholeSmoothedRemainder 1000 T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)))]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le ε) (abs_nonneg T)),
    abs_of_pos hT0]
  calc
    |‖hughesYoungActiveWholeSmoothedRemainder 1000 T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖| =
        ‖hughesYoungActiveWholeSmoothedRemainder 1000 T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ :=
      abs_of_nonneg (norm_nonneg _)
    _ ≤
        C * T := hbound hT
    _ ≤ C * (T ^ ε * T) := by
      gcongr
      nlinarith

/-- The finite equation-(83) source itself has the native fourth-moment
size.  This consumes the exact source-line continuation and both literal
truncation tails; it does not estimate the four shifted main terms
separately. -/
theorem hughesYoungFinitePureIntegratedCentral_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungFinitePureIntegratedCentral T
        (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    ((hughesYoungCompleteShiftedIntegratedCentral_epsilonPowerBound.add
      hughesYoungFiniteEquation84IntegratedShiftTail_epsilonPowerBound).add
      hughesYoungFinitePureSmallContourTail_epsilonPowerBound) ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  have hbound' := hbound.bound
  apply IsBigO.of_bound C
  filter_upwards [hbound', eventually_ge_atTop (Real.exp 3)] with T hsumT hT
  have hpure :
      hughesYoungFinitePureIntegratedCentral T (hughesYoungGlobalDepth T) =
        hughesYoungCompleteShiftedIntegratedCentral T -
          hughesYoungFiniteEquation84IntegratedShiftTail T
            (hughesYoungGlobalDepth T) -
          hughesYoungFinitePureSmallContourTail T
            (hughesYoungGlobalDepth T) := by
    rw [hughesYoungFinitePureIntegratedCentral_eq_whole_sub_tail,
      hughesYoungFinitePureWholeIntegratedCentral_eq_equation84Source hT,
      hughesYoungFiniteEquation84IntegratedSource_eq_complete_sub_shiftTail]
  have htri :
      ‖hughesYoungFinitePureIntegratedCentral T (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungCompleteShiftedIntegratedCentral T‖ +
          ‖hughesYoungFiniteEquation84IntegratedShiftTail T
            (hughesYoungGlobalDepth T)‖ +
          ‖hughesYoungFinitePureSmallContourTail T
            (hughesYoungGlobalDepth T)‖ := by
    rw [hpure]
    exact (norm_sub_le _ _).trans <|
      add_le_add (norm_sub_le _ _) le_rfl
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The exact signed source omitted when the equation-(83) finite source is
restricted to positive-coordinate dyadic boxes whose arithmetic lattices
meet the support.  Keeping this as one difference preserves the lower-scale
telescoping cancellation. -/
noncomputable def hughesYoungFiniteRegularSupportedSourceTail
    (T : ℝ) (K : ℕ) : ℂ :=
  hughesYoungFinitePureIntegratedCentral T K -
    hughesYoungRectangularRegularSupportedIntegratedCompleteCentral T K

/-- Solved form of the support-valid rectangular source. -/
theorem hughesYoungRectangularRegularSupportedIntegratedCompleteCentral_eq_pure_sub_tail
    (T : ℝ) (K : ℕ) :
    hughesYoungRectangularRegularSupportedIntegratedCompleteCentral T K =
      hughesYoungFinitePureIntegratedCentral T K -
        hughesYoungFiniteRegularSupportedSourceTail T K := by
  unfold hughesYoungFiniteRegularSupportedSourceTail
  ring

/-- The complementary source family which must be estimated as one signed
object.  It combines the dyadic endpoint, boxes outside the active
rectangle, and the actual non-large boxes before any norm is taken. -/
noncomputable def hughesYoungNativeComplementarySource
    (T P : ℝ) (R K : ℕ) : ℂ :=
  -hughesYoungFiniteEndpointIntegratedCentral T K +
    hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
    hughesYoungInactiveIntegratedCompleteCentral T R K -
    hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K

/-- The exact difference between the equation-(85) source formed on the
actual product-truncated dyadic family and the complete finite equation-(83)
source.  This is the source truncation error that Hughes--Young remove when
passing from the dyadic sum in (83) to (85). -/
noncomputable def hughesYoungActiveSourceDiscrepancy
    (T : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungActiveReassembledIntegratedCentral T R K -
    hughesYoungFinitePureIntegratedCentral T K

/-- The literal product-truncation complement in the equation-(83) Mellin
weight.  It is kept as one signed weight so that the subsequent contour move
can use cancellation before any norm is taken. -/
noncomputable def hughesYoungActiveComplementReducedMellinWeight
    (T t c u : ℝ) (h k a b R K : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungPureReducedMellinWeight T t c u h k x y -
    hughesYoungActiveReassembledReducedMellinWeight
      T t c u h k a b R K x y

/-- On the positive quadrant the missing source is exactly the common
Hughes--Young Mellin monomial multiplied by `1` minus the genuine smooth
active cutoff.  This is the source-facing form of the truncation made before
equation (61). -/
theorem hughesYoungActiveComplementReducedMellinWeight_eq_scaled_one_sub
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungActiveComplementReducedMellinWeight
        T t c u h k a b R K x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        ((1 - hughesYoungActiveContinuousDyadicWeight a b R K x y : ℝ) : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  unfold hughesYoungActiveComplementReducedMellinWeight
  rw [hughesYoungPureReducedMellinWeight_of_pos T t c u h k hx hy,
    hughesYoungActiveReassembledReducedMellinWeight_eq_scaled_powers
      T t c u hh hk a b R K hx hy]
  push_cast
  ring_nf

/-- The signed finite-shift central source carried by the product-truncation
complement.  The positive and negative shifts remain in one sum. -/
noncomputable def hughesYoungActiveComplementSignedCentralAtHeight
    (T t c u : ℝ) (h k a b R K : ℕ) : ℂ :=
  hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K -
    hughesYoungActiveReassembledSignedCentralAtHeight
      T t c u h k a b R K

/-- Exact linear decomposition of the pure equation-(83) central family into
the active family and its signed product-truncation complement. -/
theorem hughesYoungFinitePureSignedCentralAtHeight_eq_active_add_complement
    (T t c u : ℝ) (h k a b R K : ℕ) :
    hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K =
      hughesYoungActiveReassembledSignedCentralAtHeight
          T t c u h k a b R K +
        hughesYoungActiveComplementSignedCentralAtHeight
          T t c u h k a b R K := by
  unfold hughesYoungActiveComplementSignedCentralAtHeight
  ring

/-- Exact solved form of the complementary source.  It identifies the
remaining source-sized comparison as the large-DFI central subfamily minus
the complete finite equation-(83) family, together with the already
estimated literal non-large off-diagonal family. -/
theorem hughesYoungNativeComplementarySource_eq_nonLarge_add_largeCentral_sub_pure
    (T P : ℝ) (R K : ℕ) :
    hughesYoungNativeComplementarySource T P R K =
      hughesYoungActiveNonLargeDFIOffDiagonal T P R K +
        hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K -
        hughesYoungFinitePureIntegratedCentral T K := by
  rw [hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_rectangular_sub_corrections]
  unfold hughesYoungNativeComplementarySource
    hughesYoungFiniteEndpointIntegratedCentral
  ring

/-- Active-source form of the remaining native comparison.  It removes the
artificial inactive rectangular central family and isolates the literal
active source truncation error together with the exact non-large DFI pair. -/
theorem hughesYoungNativeComplementarySource_eq_nonLargePair_add_activeSourceDiscrepancy
    {T P : ℝ} (hT : Real.exp 1 ≤ T) (R K : ℕ) :
    hughesYoungNativeComplementarySource T P R K =
      hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
        hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K +
        hughesYoungActiveSourceDiscrepancy T R K := by
  rw [hughesYoungNativeComplementarySource_eq_nonLarge_add_largeCentral_sub_pure]
  rw [hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_full_sub_nonLarge]
  rw [hughesYoungActiveIntegratedCompleteCentral_eq_reassembledSource hT]
  unfold hughesYoungActiveSourceDiscrepancy
  ring

/-- Source-faithful form of the native complementary family.  The first
two terms are the literal non-large off-diagonal and its equation-(81)
central continuation.  The remaining two terms are exactly the inactive
support-valid tail and the cancellation-preserving lower/support endpoint
tail of the global signed source. -/
theorem hughesYoungNativeComplementarySource_eq_supported_tails
    (T P : ℝ) (R K : ℕ) :
    hughesYoungNativeComplementarySource T P R K =
      hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
        hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T P R K -
        hughesYoungInactiveRegularSupportedIntegratedCompleteCentral T R K -
        hughesYoungFiniteRegularSupportedSourceTail T K := by
  rw [hughesYoungNativeComplementarySource_eq_nonLarge_add_largeCentral_sub_pure]
  have hactive :=
    hughesYoungActiveRegularSupportedIntegratedCompleteCentral_eq_large_add_nonLarge
      T P R K
  have hrectangle :=
    hughesYoungRectangularRegularSupportedIntegratedCompleteCentral_eq_active_add_inactive
      T R K
  have htail :=
    hughesYoungRectangularRegularSupportedIntegratedCompleteCentral_eq_pure_sub_tail
      T K
  have hlarge :
      hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K =
        hughesYoungActiveRegularSupportedIntegratedCompleteCentral T R K -
          hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T P R K := by
    rw [hactive]
    ring
  have hactive' :
      hughesYoungActiveRegularSupportedIntegratedCompleteCentral T R K =
        hughesYoungRectangularRegularSupportedIntegratedCompleteCentral T K -
          hughesYoungInactiveRegularSupportedIntegratedCompleteCentral T R K := by
    rw [hrectangle]
    ring
  rw [hlarge, hactive', htail]
  ring

/-- The complete native off-diagonal remainder after the four shifted
Hughes--Young central terms have been kept together. -/
noncomputable def hughesYoungNativeOffDiagonalRemainder
    (T P : ℝ) (R K : ℕ) : ℂ :=
  -hughesYoungFiniteEquation84IntegratedShiftTail T K -
    hughesYoungFinitePureSmallContourTail T K +
    hughesYoungNativeComplementarySource T P R K -
    hughesYoungActiveLargeDFIIntegratedCentralTail T P R K +
    hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K +
    hughesYoungActiveLargeDFIFarOffDiagonal T P R K

/-- Exact source-order Hughes--Young off-diagonal assembly.  In
particular, the complete shifted source is not split into its four
meromorphic summands before the equality is formed. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_completeShifted_add_remainder
    {T P : ℝ} (hT : Real.exp 3 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungCompleteShiftedIntegratedCentral T +
        hughesYoungNativeOffDiagonalRemainder T P R K := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hT
  rw [hughesYoungActiveFiniteOffDiagonal_eq_rectangularCentral_add_correction
      hT1 hT16 hP hPT R K,
    hughesYoungRectangularIntegratedCompleteCentral_eq_shifted_sub_threeTails
      hT K]
  unfold hughesYoungNativeOffDiagonalRemainder
    hughesYoungNativeComplementarySource hughesYoungNativeOffDiagonalCorrection
  ring

end RiemannZeta.GuthMaynard
