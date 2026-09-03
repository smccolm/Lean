import GafniTao.PintzPhysicalErrorDischarge

/-!
# Quantitative lower bounds for the physical Pintz detector

The logarithmic reserve in `pintzDensityLambda` is kept literally.  After
multiplication by `eta`, it supplies a large positive power of `log T`; the
main term supplies the source `eta^(3/2) log T` power.
-/

namespace GafniTao

noncomputable section

theorem pintz_exp_two_lambda_eta_lower
    {eta T : ℝ} (heta : 0 < eta)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    T ^ (2 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (2 * pintzDensityLogReserve) ≤
      Real.exp (2 * pintzDensityLambda eta T * eta) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTpos hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hthresholdNonneg : 0 ≤ pintzMobiusLambdaThreshold * eta :=
    mul_nonneg pintzMobiusLambdaThreshold_pos.le heta.le
  rw [show 2 * pintzDensityLambda eta T * eta =
      2 * (pintzDensityLambda eta T * eta) by ring,
    pintzDensityLambda_mul_eta heta]
  rw [Real.rpow_def_of_pos hTpos, Real.rpow_def_of_pos hlogPos,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem pintz_eta_sq_lower
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    c ^ 2 / Real.log T ^ 2 ≤ eta ^ 2 := by
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  have hlower := pintz_eta_lower_of_above_zeroFree hc hT hetaAbove
  have hleftNonneg : 0 ≤ c / Real.log T := div_nonneg hc.le hlogPos.le
  have hetaPos : 0 < eta := (div_pos hc hlogPos).trans_le hlower
  have hsq : (c / Real.log T) ^ 2 ≤ eta ^ 2 := by nlinarith
  calc
    c ^ 2 / Real.log T ^ 2 = (c / Real.log T) ^ 2 := by
      field_simp [hlogPos.ne']
    _ ≤ eta ^ 2 := hsq

theorem pintz_exp_shift_lower
    {eta T : ℝ} (heta : 0 < eta)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    Real.exp (-1 / 2) *
        (T ^ (2 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (2 * pintzDensityLogReserve)) ≤
      Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4)) := by
  have hmain := pintz_exp_two_lambda_eta_lower heta hT
  have hnonneg : 0 ≤ Real.exp (-1 / 2) := (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-1 / 2) *
        Real.exp (2 * pintzDensityLambda eta T * eta) := by gcongr
    _ = Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring

#print axioms pintz_exp_two_lambda_eta_lower
#print axioms pintz_eta_sq_lower
#print axioms pintz_exp_shift_lower

end

end GafniTao
