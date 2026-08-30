import GafniTao.RightEdge
import GafniTao.ZeroSumSup

/-!
# Physical-scale Vinogradov--Korobov decay

This module carries the literal cutoff in the zero-free region from the
source height `T = J log(X)^2 X^(1-theta)` back to the physical `X` scale.
The safe constant `c/8` records every loss in the two logarithmic
comparisons; it is not hidden in asymptotic notation.
-/

open Filter

namespace GafniTao

/-- The stretched-exponential scale in Gafni--Tao Lemma 2.1. -/
noncomputable def vinogradovKorobovDecayScale (X : ℝ) : ℝ :=
  Real.log X ^ (1 / 3 : ℝ) /
    Real.log (Real.log X) ^ (1 / 3 : ℝ)

/-- Deterministic conversion from the literal height cutoff to physical
stretched-exponential decay under two explicit logarithmic comparisons. -/
theorem cutoff_rpow_le_stretched_exp
    {c T X : ℝ} (hc : 0 < c) (hX : Real.exp 1 < X)
    (hT : Real.exp 1 < T)
    (hlog : Real.log T ≤ 2 * Real.log X)
    (hloglog : Real.log (Real.log T) ≤
      2 * Real.log (Real.log X)) :
    X ^ (-(c / (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ))) / 2) ≤
      Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hlogXOne : 1 < Real.log X :=
    (Real.lt_log_iff_exp_lt (zero_lt_one.trans hXone)).2 hX
  have hloglogX : 0 < Real.log (Real.log X) := Real.log_pos hlogXOne
  have hTone : 1 < T := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hTone
  have hlogTOne : 1 < Real.log T :=
    (Real.lt_log_iff_exp_lt (zero_lt_one.trans hTone)).2 hT
  have hloglogT : 0 < Real.log (Real.log T) := Real.log_pos hlogTOne
  have htwo23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) (show (2 / 3 : ℝ) ≤ 1 by norm_num) using 1
    norm_num
  have htwo13 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 by norm_num) (show (1 / 3 : ℝ) ≤ 1 by norm_num) using 1
    norm_num
  have hp23 : Real.log T ^ (2 / 3 : ℝ) ≤
      2 * Real.log X ^ (2 / 3 : ℝ) := by
    calc
      Real.log T ^ (2 / 3 : ℝ) ≤
          (2 * Real.log X) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hlogT.le hlog (by norm_num)
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) *
          Real.log X ^ (2 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hlogX.le]
      _ ≤ 2 * Real.log X ^ (2 / 3 : ℝ) := by gcongr
  have hp13 : Real.log (Real.log T) ^ (1 / 3 : ℝ) ≤
      2 * Real.log (Real.log X) ^ (1 / 3 : ℝ) := by
    calc
      Real.log (Real.log T) ^ (1 / 3 : ℝ) ≤
          (2 * Real.log (Real.log X)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hloglogT.le hloglog (by norm_num)
      _ = (2 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (Real.log X) ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hloglogX.le]
      _ ≤ 2 * Real.log (Real.log X) ^ (1 / 3 : ℝ) := by gcongr
  let DT : ℝ := Real.log T ^ (2 / 3 : ℝ) *
    Real.log (Real.log T) ^ (1 / 3 : ℝ)
  let DX : ℝ := Real.log X ^ (2 / 3 : ℝ) *
    Real.log (Real.log X) ^ (1 / 3 : ℝ)
  have hDTpos : 0 < DT := by
    dsimp [DT]
    positivity
  have hDXpos : 0 < DX := by
    dsimp [DX]
    positivity
  have hden : DT ≤ 4 * DX := by
    dsimp [DT, DX]
    nlinarith [mul_le_mul hp23 hp13
      (Real.rpow_nonneg hloglogT.le _) (by positivity)]
  have hfrac : c / (4 * DX) ≤ c / DT := by
    exact div_le_div_of_nonneg_left hc.le hDTpos hden
  have hscale : Real.log X / DX = vinogradovKorobovDecayScale X := by
    dsimp [DX, vinogradovKorobovDecayScale]
    have hp : Real.log X ^ (1 / 3 : ℝ) *
        Real.log X ^ (2 / 3 : ℝ) = Real.log X := by
      rw [← Real.rpow_add hlogX]
      norm_num
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hlogX _),
      ne_of_gt (Real.rpow_pos_of_pos hloglogX _)]
    nlinarith
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hXone)]
  apply Real.exp_le_exp.mpr
  have hmain : (c / 8) * vinogradovKorobovDecayScale X ≤
      (c / DT) * Real.log X / 2 := by
    rw [← hscale]
    calc
      (c / 8) * (Real.log X / DX) =
          (c / (4 * DX)) * Real.log X / 2 := by ring
      _ ≤ (c / DT) * Real.log X / 2 := by gcongr
  dsimp [DT] at hmain ⊢
  linarith

/-- At the source height, both iterated logarithms cost a factor at most two
on the physical scale. -/
theorem eventually_explicitFormulaHeight_log_comparisons
    {J theta : ℝ} (hJ : 0 < J) (hthetaLower : 0 < theta)
    (hthetaUpper : theta < 1) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 1 < explicitFormulaHeight J theta X ∧
      Real.log (explicitFormulaHeight J theta X) ≤ 2 * Real.log X ∧
      Real.log (Real.log (explicitFormulaHeight J theta X)) ≤
        2 * Real.log (Real.log X) := by
  have hHeightTop := tendsto_explicitFormulaHeight_atTop hJ hthetaUpper
  have hHeightLarge : ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 1 < explicitFormulaHeight J theta X :=
    hHeightTop.eventually (Filter.eventually_gt_atTop (Real.exp 1))
  have hq : 0 < 1 + theta := by linarith
  have hHeightBound := eventually_explicitFormulaHeight_le_rpow
    (J := J) (theta := theta) hq
  filter_upwards [hHeightLarge, hHeightBound,
      Filter.eventually_ge_atTop (Real.exp 2)] with X hTLarge hTBound hX
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXtwo : 2 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hX
  have hTpos : 0 < explicitFormulaHeight J theta X :=
    (Real.exp_pos 1).trans hTLarge
  have hTPow : explicitFormulaHeight J theta X ≤ X ^ (2 : ℝ) := by
    simpa only [show 1 - theta + (1 + theta) = (2 : ℝ) by ring] using hTBound
  have hlog : Real.log (explicitFormulaHeight J theta X) ≤
      2 * Real.log X := by
    calc
      Real.log (explicitFormulaHeight J theta X) ≤ Real.log (X ^ (2 : ℝ)) :=
        Real.log_le_log hTpos hTPow
      _ = 2 * Real.log X := Real.log_rpow hXpos 2
  have hlogTOne : 1 < Real.log (explicitFormulaHeight J theta X) :=
    (Real.lt_log_iff_exp_lt hTpos).2 hTLarge
  have hloglog :
      Real.log (Real.log (explicitFormulaHeight J theta X)) ≤
        2 * Real.log (Real.log X) := by
    calc
      Real.log (Real.log (explicitFormulaHeight J theta X)) ≤
          Real.log (2 * Real.log X) :=
        Real.log_le_log (zero_lt_one.trans hlogTOne) hlog
      _ = Real.log 2 + Real.log (Real.log X) := by
        rw [Real.log_mul (by norm_num) hlogXpos.ne']
      _ ≤ 2 * Real.log (Real.log X) := by
        have hlog2 : Real.log 2 ≤ Real.log (Real.log X) :=
          Real.log_le_log (by norm_num) hlogXtwo
        linarith
  exact ⟨hTLarge, hlog, hloglog⟩

/-- The literal Vinogradov--Korobov cutoff at the source height has the
paper's stretched-exponential physical decay, with an explicit safe constant.
-/
theorem eventually_physical_vinogradovKorobov_cutoff_decay
    {J theta c : ℝ} (hJ : 0 < J) (hthetaLower : 0 < theta)
    (hthetaUpper : theta < 1) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop,
      X ^ (-(c /
        (Real.log (explicitFormulaHeight J theta X) ^ (2 / 3 : ℝ) *
          Real.log (Real.log (explicitFormulaHeight J theta X)) ^
            (1 / 3 : ℝ))) / 2) ≤
        Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
  filter_upwards [eventually_explicitFormulaHeight_log_comparisons
      hJ hthetaLower hthetaUpper,
      Filter.eventually_gt_atTop (Real.exp 1)] with X h hX
  exact cutoff_rpow_le_stretched_exp hc hX h.1 h.2.1 h.2.2

/-- The Vinogradov--Korobov scale dominates a fixed positive power of
`log X`.  This is the quantitative bridge used to absorb every fixed
logarithmic prefactor. -/
theorem eventually_rpow_log_le_vinogradovKorobovDecayScale :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.log X ^ (1 / 6 : ℝ) ≤ vinogradovKorobovDecayScale X := by
  have hLittle := (isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
      Real.tendsto_log_atTop
  filter_upwards [hLittle.eventuallyLE,
      Filter.eventually_ge_atTop (Real.exp (Real.exp 1))] with X hlog hX
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have htOne : 1 ≤ Real.log X := by
    have : Real.exp 1 ≤ X := (Real.exp_le_exp.mpr (by
      exact (show (1 : ℝ) ≤ Real.exp 1 from
        (Real.one_lt_exp_iff.mpr zero_lt_one).le))).trans hX
    exact (Real.le_log_iff_exp_le hXpos).2 this
  have huOne : 1 ≤ Real.log (Real.log X) := by
    have hlogXpos : 0 < Real.log X := zero_lt_one.trans_le htOne
    exact (Real.le_log_iff_exp_le hlogXpos).2 (by
      simpa using (Real.le_log_iff_exp_le hXpos).2 hX)
  have htPos : 0 < Real.log X := zero_lt_one.trans_le htOne
  have huPos : 0 < Real.log (Real.log X) := zero_lt_one.trans_le huOne
  have hlog' : Real.log (Real.log X) ≤ Real.log X ^ (1 / 2 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg htOne),
      abs_of_nonneg (Real.log_nonneg htOne),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans htOne) _)] using hlog
  have hden : Real.log (Real.log X) ^ (1 / 3 : ℝ) ≤
      Real.log X ^ (1 / 6 : ℝ) := by
    calc
      Real.log (Real.log X) ^ (1 / 3 : ℝ) ≤
          (Real.log X ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow huPos.le hlog' (by norm_num)
      _ = Real.log X ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_mul htPos.le]
        norm_num
  have hpow : Real.log X ^ (1 / 6 : ℝ) *
      Real.log X ^ (1 / 6 : ℝ) =
        Real.log X ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add htPos]
    norm_num
  rw [vinogradovKorobovDecayScale]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos huPos _)]
  calc
    Real.log X ^ (1 / 6 : ℝ) *
        Real.log (Real.log X) ^ (1 / 3 : ℝ) ≤
      Real.log X ^ (1 / 6 : ℝ) *
        Real.log X ^ (1 / 6 : ℝ) := by gcongr
    _ = Real.log X ^ (1 / 3 : ℝ) := hpow

/-- The physical Vinogradov--Korobov decay scale tends to infinity. -/
theorem tendsto_vinogradovKorobovDecayScale_atTop :
    Filter.Tendsto vinogradovKorobovDecayScale
      Filter.atTop Filter.atTop := by
  have hBase : Filter.Tendsto
      (fun X : ℝ => Real.log X ^ (1 / 6 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp
      Real.tendsto_log_atTop
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hBase
  exact eventually_rpow_log_le_vinogradovKorobovDecayScale

/-- Every fixed real power of the source-height logarithm is eventually
absorbed by half of the safe physical stretched-exponential saving. -/
theorem eventually_log_prefactor_le_stretched_exp
    {J theta B c : ℝ} (hJ : 0 < J) (hthetaLower : 0 < theta)
    (hthetaUpper : theta < 1) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop,
      6 * Real.log (explicitFormulaHeight J theta X) ^ B ≤
        Real.exp ((c / 16) * vinogradovKorobovDecayScale X) := by
  let Bp : ℝ := max B 0
  let K : ℝ := 6 * (2 : ℝ) ^ Bp
  let y : ℝ → ℝ := fun X => Real.log X ^ (1 / 6 : ℝ)
  have hBp : 0 ≤ Bp := le_max_right _ _
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < c / 16 := by positivity
  have hyTop : Filter.Tendsto y Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp
      Real.tendsto_log_atTop
  have hLittle := (isLittleO_rpow_exp_pos_mul_atTop (6 * Bp) hb).comp_tendsto hyTop
  have hBound := hLittle.bound (one_div_pos.mpr hK)
  filter_upwards [hBound,
      eventually_explicitFormulaHeight_log_comparisons hJ hthetaLower hthetaUpper,
      eventually_rpow_log_le_vinogradovKorobovDecayScale,
      Filter.eventually_ge_atTop (Real.exp (Real.exp 1))] with
      X hBoundX hHeight hScale hX
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have htOne : 1 ≤ Real.log X := by
    have hExpOneX : Real.exp 1 ≤ X := by
      calc
        Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr
          (Real.one_lt_exp_iff.mpr zero_lt_one).le
        _ ≤ X := hX
    exact (Real.le_log_iff_exp_le hXpos).2 hExpOneX
  have hXone : 1 < X := by
    calc
      1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
      _ ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le
      _ ≤ X := hX
  have hTpos : 0 < explicitFormulaHeight J theta X :=
    explicitFormulaHeight_pos hJ hXone
  have hTlogOne : 1 ≤ Real.log (explicitFormulaHeight J theta X) :=
    ((Real.lt_log_iff_exp_lt hTpos).2 hHeight.1).le
  have hTheightOne : 1 ≤ explicitFormulaHeight J theta X :=
    hHeight.1.le.trans' (Real.one_lt_exp_iff.mpr zero_lt_one).le
  have hB : B ≤ Bp := le_max_left _ _
  have hBasePow : Real.log (explicitFormulaHeight J theta X) ^ B ≤
      Real.log (explicitFormulaHeight J theta X) ^ Bp :=
    Real.rpow_le_rpow_of_exponent_le hTlogOne hB
  have hLogPow : Real.log (explicitFormulaHeight J theta X) ^ Bp ≤
      (2 * Real.log X) ^ Bp :=
    Real.rpow_le_rpow (Real.log_nonneg hTheightOne) hHeight.2.1 hBp
  have hyPow : y X ^ (6 * Bp) = Real.log X ^ Bp := by
    dsimp [y]
    rw [← Real.rpow_mul (zero_le_one.trans htOne)]
    congr 1
    ring
  have hMain : K * Real.log X ^ Bp ≤ Real.exp ((c / 16) * y X) := by
    have hBound' : y X ^ (6 * Bp) ≤
        (1 / K) * Real.exp ((c / 16) * y X) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ y X) _),
        abs_of_nonneg (Real.exp_pos _).le] using hBoundX
    rw [← hyPow]
    calc
      K * y X ^ (6 * Bp) ≤
          K * ((1 / K) * Real.exp ((c / 16) * y X)) := by gcongr
      _ = Real.exp ((c / 16) * y X) := by field_simp [hK.ne']
  calc
    6 * Real.log (explicitFormulaHeight J theta X) ^ B ≤
        6 * Real.log (explicitFormulaHeight J theta X) ^ Bp := by gcongr
    _ ≤ 6 * (2 * Real.log X) ^ Bp := by gcongr
    _ = K * Real.log X ^ Bp := by
      dsimp [K]
      calc
        6 * (2 * Real.log X) ^ Bp =
            6 * ((2 : ℝ) ^ Bp * Real.log X ^ Bp) := by
          rw [Real.mul_rpow (x := 2) (y := Real.log X) (z := Bp)
            (by norm_num) (zero_le_one.trans htOne)]
        _ = 6 * (2 : ℝ) ^ Bp * Real.log X ^ Bp := by ring
    _ ≤ Real.exp ((c / 16) * y X) := hMain
    _ ≤ Real.exp ((c / 16) * vinogradovKorobovDecayScale X) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hScale (by positivity)

/-- The literal cutoff occurring in the Vinogradov--Korobov zero-free
region after substituting the Gafni--Tao source height. -/
noncomputable def physicalVinogradovKorobovCutoff
    (J theta c X : ℝ) : ℝ :=
  c / (Real.log (explicitFormulaHeight J theta X) ^ (2 / 3 : ℝ) *
    Real.log (Real.log (explicitFormulaHeight J theta X)) ^ (1 / 3 : ℝ))

/-- Fixed right-edge width used to optimize the near-one density exponent. -/
noncomputable def nearOneRightEdgeWidth (C q : ℝ) : ℝ :=
  min (1 / 2) ((1 / (2 * q * C)) ^ (2 : ℕ))

theorem nearOneRightEdgeWidth_pos {C q : ℝ} (hC : 0 < C) (hq : 0 < q) :
    0 < nearOneRightEdgeWidth C q := by
  unfold nearOneRightEdgeWidth
  exact lt_min (by norm_num) (sq_pos_of_pos (by positivity))

theorem nearOneRightEdgeWidth_le_half (C q : ℝ) :
    nearOneRightEdgeWidth C q ≤ 1 / 2 := min_le_left _ _

theorem nearOneRightEdgeWidth_le_small (C q : ℝ) :
    nearOneRightEdgeWidth C q ≤ (1 / (2 * q * C)) ^ (2 : ℕ) :=
  min_le_right _ _

/-- The denominator in the physical Vinogradov--Korobov cutoff tends to
infinity at the actual source height. -/
theorem tendsto_physicalVinogradovKorobovDenominator_atTop
    {J theta : ℝ} (hJ : 0 < J) (htheta : theta < 1) :
    Filter.Tendsto (fun X : ℝ =>
      Real.log (explicitFormulaHeight J theta X) ^ (2 / 3 : ℝ) *
        Real.log (Real.log (explicitFormulaHeight J theta X)) ^
          (1 / 3 : ℝ)) Filter.atTop Filter.atTop := by
  have hHeight := tendsto_explicitFormulaHeight_atTop hJ htheta
  have hLog : Filter.Tendsto (fun X : ℝ =>
      Real.log (explicitFormulaHeight J theta X)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hHeight
  have hLogLog : Filter.Tendsto (fun X : ℝ =>
      Real.log (Real.log (explicitFormulaHeight J theta X)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hLog
  have hFirst : Filter.Tendsto (fun X : ℝ =>
      Real.log (explicitFormulaHeight J theta X) ^ (2 / 3 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).comp hLog
  have hSecond : ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ Real.log (Real.log (explicitFormulaHeight J theta X)) ^
        (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
      hLogLog).eventually (Filter.eventually_ge_atTop 1)
  apply tendsto_atTop_mono' Filter.atTop _ hFirst
  filter_upwards [hSecond,
      hFirst.eventually (Filter.eventually_ge_atTop 0)] with X hs hf
  nlinarith

theorem tendsto_physicalVinogradovKorobovCutoff_zero
    {J theta c : ℝ} (hJ : 0 < J) (htheta : theta < 1) :
    Filter.Tendsto (physicalVinogradovKorobovCutoff J theta c)
      Filter.atTop (nhds 0) := by
  have hDen := tendsto_physicalVinogradovKorobovDenominator_atTop hJ htheta
  have hInv := tendsto_inv_atTop_zero.comp hDen
  have hMul : Filter.Tendsto (fun X : ℝ => c *
      (Real.log (explicitFormulaHeight J theta X) ^ (2 / 3 : ℝ) *
        Real.log (Real.log (explicitFormulaHeight J theta X)) ^
          (1 / 3 : ℝ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_const_nhds (x := c)).mul hInv
  apply hMul.congr'
  filter_upwards [] with X
  simp only [physicalVinogradovKorobovCutoff, div_eq_mul_inv]

/-- Eventually the literal physical cutoff is positive and lies inside any
fixed positive right-edge width. -/
theorem eventually_physicalVinogradovKorobovCutoff_data
    {J theta c eta₀ : ℝ} (hJ : 0 < J) (htheta : theta < 1)
    (hc : 0 < c) (heta₀ : 0 < eta₀) :
    ∀ᶠ X : ℝ in Filter.atTop,
      0 < physicalVinogradovKorobovCutoff J theta c X ∧
      physicalVinogradovKorobovCutoff J theta c X ≤ eta₀ := by
  have hSmall := (tendsto_physicalVinogradovKorobovCutoff_zero
    (c := c) hJ htheta).eventually (Iio_mem_nhds heta₀)
  filter_upwards [hSmall,
      (tendsto_explicitFormulaHeight_atTop hJ htheta).eventually
        (Filter.eventually_gt_atTop (Real.exp 1))] with X hSmall hHeight
  have hlog : 0 < Real.log (explicitFormulaHeight J theta X) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hHeight)
  have hTpos : 0 < explicitFormulaHeight J theta X :=
    (Real.exp_pos 1).trans hHeight
  have hlogOne : 1 < Real.log (explicitFormulaHeight J theta X) :=
    (Real.lt_log_iff_exp_lt hTpos).2 hHeight
  have hloglog : 0 < Real.log (Real.log (explicitFormulaHeight J theta X)) :=
    Real.log_pos hlogOne
  constructor
  · unfold physicalVinogradovKorobovCutoff
    positivity
  · exact hSmall.le

/-- Pointwise physical form of the right-edge estimate.  The final displayed
hypothesis is exactly the remaining elementary absorption of the fixed
logarithmic prefactor; all analytic inputs and the literal cutoff have
already been consumed by this theorem. -/
theorem norm_rightEdgeZeroSum_le_physical_stretched_exp
    {C B T₀ c T₁ q eta₀ d T tau X x : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c) (hq : 0 < q)
    (hdPos : 0 < d) (hdUpper : d ≤ eta₀)
    (hdVK : d = c /
      (Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ)))
    (heta₀Upper : eta₀ ≤ 1 / 2)
    (heta₀Small : eta₀ ≤ (1 / (2 * q * C)) ^ (2 : ℕ))
    (hT₀ : T₀ ≤ T) (hT₁ : T₁ ≤ T)
    (hTexp : Real.exp 1 < T)
    (htau : 0 < tau) (hXexp : Real.exp 1 < X)
    (hTscale : T ≤ X ^ q)
    (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X)
    (hlog : Real.log T ≤ 2 * Real.log X)
    (hloglog : Real.log (Real.log T) ≤
      2 * Real.log (Real.log X))
    (hAbsorb : 6 * Real.log T ^ B ≤
      Real.exp ((c / 16) * vinogradovKorobovDecayScale X)) :
    ‖zeroStripIncrementSum (1 - eta₀) 1 T tau x‖ ≤
      (X / tau) *
        Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hXexp
  have hTone : 1 ≤ T :=
    ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hTexp).le
  have hRaw := norm_rightEdgeZeroSum_le_vinogradovKorobov_decay
    hDensity hZeroFree hC hq hdPos hdUpper hdVK heta₀Upper heta₀Small
      hT₀ hT₁ hTone htau hXone hTscale hxLower hxUpper
  have hCut : X ^ (-d / 2) ≤
      Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
    rw [hdVK]
    exact cutoff_rpow_le_stretched_exp hc hXexp hTexp hlog hloglog
  have hXTau : 0 ≤ X / tau := by positivity
  have hL : 0 ≤ Real.log T ^ B :=
    Real.rpow_nonneg (Real.log_nonneg hTone) B
  have hExp : 0 ≤
      Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) :=
    (Real.exp_pos _).le
  calc
    ‖zeroStripIncrementSum (1 - eta₀) 1 T tau x‖ ≤
        (6 * X / tau) * Real.log T ^ B * X ^ (-d / 2) := hRaw
    _ ≤ (6 * X / tau) * Real.log T ^ B *
        Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by gcongr
    _ = (X / tau) * (6 * Real.log T ^ B) *
        Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by ring
    _ ≤ (X / tau) *
        Real.exp ((c / 16) * vinogradovKorobovDecayScale X) *
          Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by gcongr
    _ = (X / tau) *
        Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Full source-scale conclusion of the right-edge argument, conditional only
on the two exact published analytic input predicates.  All choices of width,
height, cutoff, exponent margin, logarithmic losses, and physical-scale
comparisons are discharged here, uniformly for `X ≤ x ≤ 2X`. -/
theorem eventually_norm_rightEdgeZeroSum_le_physical_stretched_exp
    {C B T₀ c T₁ J theta : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c) (hJ : 0 < J)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      ‖zeroStripIncrementSum
          (1 - nearOneRightEdgeWidth C 2) 1
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
        (X / localTau X theta) *
          Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by
  have hWidth : 0 < nearOneRightEdgeWidth C 2 :=
    nearOneRightEdgeWidth_pos hC (by norm_num)
  have hCutoff := eventually_physicalVinogradovKorobovCutoff_data
    hJ hthetaUpper hc hWidth
  have hLogs := eventually_explicitFormulaHeight_log_comparisons
    hJ hthetaLower hthetaUpper
  have hAbsorb := eventually_log_prefactor_le_stretched_exp
    (B := B) (c := c) hJ hthetaLower hthetaUpper hc
  have hHeightLarge : ∀ᶠ X : ℝ in Filter.atTop,
      max T₀ T₁ ≤ explicitFormulaHeight J theta X :=
    (tendsto_explicitFormulaHeight_atTop hJ hthetaUpper).eventually
      (Filter.eventually_ge_atTop _)
  have hq : 0 < 1 + theta := by linarith
  have hHeightPower := eventually_explicitFormulaHeight_le_rpow
    (J := J) (theta := theta) hq
  filter_upwards [hCutoff, hLogs, hAbsorb, hHeightLarge, hHeightPower,
      Filter.eventually_gt_atTop (Real.exp 1)] with
      X hCut hLog hAbs hThresholds hPower hX
  intro x hxLower hxUpper
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hTscale : explicitFormulaHeight J theta X ≤ X ^ (2 : ℝ) := by
    simpa only [show 1 - theta + (1 + theta) = (2 : ℝ) by ring] using hPower
  apply norm_rightEdgeZeroSum_le_physical_stretched_exp
    hDensity hZeroFree hC hc (by norm_num : (0 : ℝ) < 2)
    hCut.1 hCut.2 rfl
    (nearOneRightEdgeWidth_le_half C 2)
    (nearOneRightEdgeWidth_le_small C 2)
    (le_max_left _ _ |>.trans hThresholds)
    (le_max_right _ _ |>.trans hThresholds)
    hLog.1 (localTau_pos hXpos) hX hTscale
    hxLower hxUpper hLog.2.1 hLog.2.2 hAbs

/-- Cancellation-free physical right-edge estimate.  This is the reusable
form needed for any half-open strip contained in the fixed right-edge band:
twice the complete multiplicity-weighted absolute mass has the same
stretched-exponential saving as Lemma 2.1. -/
theorem eventually_two_mul_rightEdgeZeroWeight_le_physical_stretched_exp
    {C B T₀ c T₁ J theta : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c) (hJ : 0 < J)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 * rightEdgeZeroWeight (nearOneRightEdgeWidth C 2)
          (explicitFormulaHeight J theta X) X ≤
        Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by
  have hWidth : 0 < nearOneRightEdgeWidth C 2 :=
    nearOneRightEdgeWidth_pos hC (by norm_num)
  have hCutoff := eventually_physicalVinogradovKorobovCutoff_data
    hJ hthetaUpper hc hWidth
  have hLogs := eventually_explicitFormulaHeight_log_comparisons
    hJ hthetaLower hthetaUpper
  have hAbsorb := eventually_log_prefactor_le_stretched_exp
    (B := B) (c := c) hJ hthetaLower hthetaUpper hc
  have hHeightLarge : ∀ᶠ X : ℝ in Filter.atTop,
      max T₀ T₁ ≤ explicitFormulaHeight J theta X :=
    (tendsto_explicitFormulaHeight_atTop hJ hthetaUpper).eventually
      (Filter.eventually_ge_atTop _)
  have hHeightPower := eventually_explicitFormulaHeight_le_rpow
    (J := J) (theta := theta) (show 0 < 1 + theta by linarith)
  filter_upwards [hCutoff, hLogs, hAbsorb, hHeightLarge, hHeightPower,
      Filter.eventually_gt_atTop (Real.exp 1)] with
      X hCut hLog hAbs hThresholds hPower hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hTone : 1 ≤ explicitFormulaHeight J theta X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hLog.1.le
  have hTscale : explicitFormulaHeight J theta X ≤ X ^ (2 : ℝ) := by
    simpa only [show 1 - theta + (1 + theta) = (2 : ℝ) by ring] using hPower
  have hWeight := rightEdgeZeroWeight_le_vinogradovKorobov_decay
    hDensity hZeroFree hC (by norm_num : (0 : ℝ) < 2)
      hCut.1 hCut.2 rfl
      (nearOneRightEdgeWidth_le_half C 2)
      (nearOneRightEdgeWidth_le_small C 2)
      (le_max_left _ _ |>.trans hThresholds)
      (le_max_right _ _ |>.trans hThresholds)
      hTone ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hX) hTscale
  have hCutDecay : X ^ (-physicalVinogradovKorobovCutoff J theta c X / 2) ≤
      Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
    unfold physicalVinogradovKorobovCutoff
    exact cutoff_rpow_le_stretched_exp hc hX hLog.1 hLog.2.1 hLog.2.2
  have hLogPow : 0 ≤ Real.log (explicitFormulaHeight J theta X) ^ B :=
    Real.rpow_nonneg (Real.log_nonneg hTone) B
  calc
    2 * rightEdgeZeroWeight (nearOneRightEdgeWidth C 2)
          (explicitFormulaHeight J theta X) X ≤
        2 * (3 * Real.log (explicitFormulaHeight J theta X) ^ B *
          X ^ (-physicalVinogradovKorobovCutoff J theta c X / 2)) := by
      gcongr
    _ ≤ 6 * Real.log (explicitFormulaHeight J theta X) ^ B *
          Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
      rw [show 2 * (3 * Real.log (explicitFormulaHeight J theta X) ^ B *
          X ^ (-physicalVinogradovKorobovCutoff J theta c X / 2)) =
        (6 * Real.log (explicitFormulaHeight J theta X) ^ B) *
          X ^ (-physicalVinogradovKorobovCutoff J theta c X / 2) by ring]
      gcongr
    _ ≤ Real.exp ((c / 16) * vinogradovKorobovDecayScale X) *
          Real.exp (-(c / 8) * vinogradovKorobovDecayScale X) := by
      gcongr
    _ = Real.exp (-(c / 16) * vinogradovKorobovDecayScale X) := by
      rw [← Real.exp_add]
      congr 1
      ring

end GafniTao
