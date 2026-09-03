import GafniTao.PintzCountNative

/-!
# The moving cutoff raised to `4 eta`

This is the principal power-bearing factor remaining in the native finite
density inequality.  Its exact ceiling is converted to the source power
`T^(4 L eta^(3/2))` with all residual dependence retained as a fixed
coefficient and a power of `log T`.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzCutoffPowerCoefficient : ℝ :=
  2 * Real.exp (3 / 2 + pintzMobiusLambdaThreshold / 2)

theorem pintzCutoffPowerCoefficient_pos :
    0 < pintzCutoffPowerCoefficient := by
  unfold pintzCutoffPowerCoefficient
  positivity

theorem pintz_cutoff_rpow_four_eta_le
    {eta T : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^ (4 * eta) ≤
      pintzCutoffPowerCoefficient *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (4 * pintzDensityLogReserve) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTpos hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hExpOne : Real.exp 1 ≤ T := by
    exact (Real.exp_le_exp.mpr
      (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
  have hlambdaPos := pintzDensityLambda_pos heta.le hExpOne
  have hcutoff := pintzMobiusCutoff_rpow_le
    (a := 4 * eta) (by linarith : -3 ≤ pintzDensityLambda eta T)
    (by positivity : 0 ≤ 4 * eta)
  have htwo : (2 : ℝ) ^ (4 * eta) ≤ 2 := by
    have hExp : 4 * eta ≤ 1 := by linarith
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hExp
  have hLambdaEq := pintzDensityLambda_mul_eta (T := T) heta
  have hExpRemainder :
      Real.exp (12 * eta + 4 * pintzMobiusLambdaThreshold * eta) ≤
        Real.exp (3 / 2 + pintzMobiusLambdaThreshold / 2) := by
    apply Real.exp_le_exp.mpr
    have hthreshold := pintzMobiusLambdaThreshold_pos
    nlinarith
  have hExpIdentity :
      Real.exp (4 * (pintzDensityLambda eta T + 3) * eta) =
        T ^ (4 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (4 * pintzDensityLogReserve) *
          Real.exp (12 * eta + 4 * pintzMobiusLambdaThreshold * eta) := by
    rw [show 4 * (pintzDensityLambda eta T + 3) * eta =
        4 * (pintzDensityLambda eta T * eta) + 12 * eta by ring,
      hLambdaEq]
    rw [Real.rpow_def_of_pos hTpos, Real.rpow_def_of_pos hlogPos]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^ (4 * eta) ≤
        (2 * Real.exp (pintzDensityLambda eta T + 3)) ^ (4 * eta) := hcutoff
    _ = (2 : ℝ) ^ (4 * eta) *
        Real.exp (4 * (pintzDensityLambda eta T + 3) * eta) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      ring
    _ ≤ 2 *
        (T ^ (4 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (4 * pintzDensityLogReserve) *
          Real.exp (3 / 2 + pintzMobiusLambdaThreshold / 2)) := by
      rw [hExpIdentity]
      gcongr
    _ = pintzCutoffPowerCoefficient *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (4 * pintzDensityLogReserve) := by
      unfold pintzCutoffPowerCoefficient
      ring

#print axioms pintz_cutoff_rpow_four_eta_le

end

end GafniTao
