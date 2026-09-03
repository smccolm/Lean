import GafniTao.PintzParameters

/-!
# Uniform parameter bounds above the Vinogradov--Korobov boundary

These lemmas convert failure of the zero-free alternative into elementary
lower bounds for `eta` and upper bounds for the detector length.  They are
the uniformity bridge needed before the Pintz estimate can be quantified in
both `eta` and `T`.
-/

namespace GafniTao

noncomputable section

theorem vinogradovKorobovDenominator_le_log
    {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) :
    vinogradovKorobovDenominator T ≤ Real.log T := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hxLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTpos hT
  have hxPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hxLower
  have hxOne : 1 ≤ Real.log T :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hxLower
  have hlogxPos : 0 < Real.log (Real.log T) := by
    exact Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hxLower)
  have hlogxLe : Real.log (Real.log T) ≤ Real.log T :=
    Real.log_le_sub_one_of_pos hxPos |>.trans (by linarith)
  have hfirst :
      Real.log T ^ (2 / 3 : ℝ) ≤ Real.log T ^ (2 / 3 : ℝ) := le_rfl
  have hsecond :
      Real.log (Real.log T) ^ (1 / 3 : ℝ) ≤
        Real.log T ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogxPos.le hlogxLe (by norm_num)
  unfold vinogradovKorobovDenominator
  calc
    Real.log T ^ (2 / 3 : ℝ) *
        Real.log (Real.log T) ^ (1 / 3 : ℝ) ≤
      Real.log T ^ (2 / 3 : ℝ) *
        Real.log T ^ (1 / 3 : ℝ) := by gcongr
    _ = Real.log T ^ ((2 / 3 : ℝ) + 1 / 3) := by
      rw [Real.rpow_add hxPos]
    _ = Real.log T := by norm_num

theorem pintz_eta_lower_of_above_zeroFree
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    c / Real.log T ≤ eta := by
  have hDpos := vinogradovKorobovDenominator_pos hT
  have hlogPos : 0 < Real.log T := by
    have := vinogradovKorobovDenominator_le_log hT
    linarith
  have hDle := vinogradovKorobovDenominator_le_log hT
  have hfrac : c / Real.log T ≤
      c / vinogradovKorobovDenominator T :=
    div_le_div_of_nonneg_left hc.le hDpos hDle
  exact hfrac.trans hetaAbove.le

theorem pintz_eta_reciprocal_le_log
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    1 / eta ≤ Real.log T / c := by
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  have hlower := pintz_eta_lower_of_above_zeroFree hc hT hetaAbove
  calc
    1 / eta ≤ 1 / (c / Real.log T) :=
      one_div_le_one_div_of_le (div_pos hc hlogPos) hlower
    _ = Real.log T / c := by field_simp [hc.ne', hlogPos.ne']

noncomputable def pintzDensityLambdaLogCoefficient (c : ℝ) : ℝ :=
  pintzDensityLambdaCoefficient + pintzDensityLogReserve / c +
    pintzMobiusLambdaThreshold

theorem pintzDensityLambdaLogCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzDensityLambdaLogCoefficient c := by
  unfold pintzDensityLambdaLogCoefficient
  have hL := pintzDensityLambdaCoefficient_pos
  have hD := pintzDensityLogReserve_pos
  have hthreshold := pintzMobiusLambdaThreshold_pos
  have hdiv : 0 < pintzDensityLogReserve / c := div_pos hD hc
  linarith

theorem pintzDensityLambda_le_log_sq
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzDensityLambda eta T ≤
      pintzDensityLambdaLogCoefficient c * Real.log T ^ 2 := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTpos hT
  have hlogOne : 1 ≤ Real.log T :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hlogLower
  have hlogNonneg : 0 ≤ Real.log T := zero_le_one.trans hlogOne
  have hloglogNonneg : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogOne
  have hloglogLe : Real.log (Real.log T) ≤ Real.log T := by
    exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlogOne)).trans
      (by linarith)
  have hsqrt : Real.sqrt eta ≤ 1 := by
    have hsqrtSq := Real.sq_sqrt heta.le
    have hsqrtNonneg := Real.sqrt_nonneg eta
    nlinarith
  have hrecip := pintz_eta_reciprocal_le_log hc hT hetaAbove
  have hfirst :
      pintzDensityLambdaCoefficient * Real.sqrt eta * Real.log T ≤
        pintzDensityLambdaCoefficient * Real.log T ^ 2 := by
    calc
      pintzDensityLambdaCoefficient * Real.sqrt eta * Real.log T ≤
          pintzDensityLambdaCoefficient * 1 * Real.log T := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt pintzDensityLambdaCoefficient_pos.le)
          hlogNonneg
      _ ≤ pintzDensityLambdaCoefficient * Real.log T ^ 2 := by
        have hL := pintzDensityLambdaCoefficient_pos.le
        have hx : Real.log T ≤ Real.log T ^ 2 := by nlinarith
        simpa using mul_le_mul_of_nonneg_left hx hL
  have hsecond :
      pintzDensityLogReserve * Real.log (Real.log T) / eta ≤
        (pintzDensityLogReserve / c) * Real.log T ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      pintzDensityLogReserve * Real.log (Real.log T) * eta⁻¹ ≤
          pintzDensityLogReserve * Real.log T * (Real.log T / c) := by
        have hInv : eta⁻¹ ≤ Real.log T / c := by
          simpa [one_div] using hrecip
        have hD : 0 ≤ pintzDensityLogReserve :=
          pintzDensityLogReserve_pos.le
        have hleft : 0 ≤
            pintzDensityLogReserve * Real.log (Real.log T) :=
          mul_nonneg hD hloglogNonneg
        have hmiddle :
            pintzDensityLogReserve * Real.log (Real.log T) ≤
              pintzDensityLogReserve * Real.log T :=
          mul_le_mul_of_nonneg_left hloglogLe hD
        exact mul_le_mul hmiddle hInv (inv_nonneg.mpr heta.le)
          (mul_nonneg hD hlogNonneg)
      _ = (pintzDensityLogReserve / c) * Real.log T ^ 2 := by ring
  have hthreshold : pintzMobiusLambdaThreshold ≤
      pintzMobiusLambdaThreshold * Real.log T ^ 2 := by
    have hthresholdNonneg := pintzMobiusLambdaThreshold_pos.le
    have honeSq : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left honeSq hthresholdNonneg
  unfold pintzDensityLambda pintzDensityLambdaLogCoefficient
  linarith

#print axioms vinogradovKorobovDenominator_le_log
#print axioms pintz_eta_reciprocal_le_log
#print axioms pintzDensityLambda_le_log_sq

end

end GafniTao
