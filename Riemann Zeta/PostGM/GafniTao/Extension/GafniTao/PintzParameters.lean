import GafniTao.PintzCutoffBounds

/-!
# Quantitative parameters for the corrected Pintz detector

The source choice `lambda \asymp sqrt(eta) log T` supplies the power saving.
The additional `(log log T) / eta` term pays for fixed constants and
logarithmic factors uniformly down to the Vinogradov--Korobov boundary.  It
changes `lambda * eta` only by a power of `log T`, and therefore does not
alter the required `eta^(3/2)` density exponent.
-/

namespace GafniTao

noncomputable section

/-- A deliberately generous coefficient for the source power-saving term. -/
noncomputable def pintzDensityLambdaCoefficient : ℝ :=
  256 * (1 + fordSourceB 3000000)

/-- Logarithmic reserve in the detector length. -/
noncomputable def pintzDensityLogReserve : ℝ := 64

/-- Separation exponent.  This dominates the long-cutoff terminal shells. -/
noncomputable def pintzDensitySeparationCoefficient : ℝ :=
  32 * pintzDensityLambdaCoefficient +
    256 * (1 + fordSourceB 3000000)

noncomputable def pintzDensityLambda (eta T : ℝ) : ℝ :=
  pintzDensityLambdaCoefficient * Real.sqrt eta * Real.log T +
    pintzDensityLogReserve * Real.log (Real.log T) / eta +
    pintzMobiusLambdaThreshold

noncomputable def pintzDensitySeparation (eta T : ℝ) : ℝ :=
  3 + T ^ (pintzDensitySeparationCoefficient *
      eta ^ (3 / 2 : ℝ)) *
    Real.log T ^ pintzDensityLogReserve

theorem pintzDensityLambdaCoefficient_pos :
    0 < pintzDensityLambdaCoefficient := by
  unfold pintzDensityLambdaCoefficient
  have hB := four_le_fordSourceB_three_million
  positivity

theorem pintzDensityLogReserve_pos : 0 < pintzDensityLogReserve := by
  norm_num [pintzDensityLogReserve]

theorem pintzDensitySeparationCoefficient_pos :
    0 < pintzDensitySeparationCoefficient := by
  unfold pintzDensitySeparationCoefficient
  have hL := pintzDensityLambdaCoefficient_pos
  have hB := four_le_fordSourceB_three_million
  positivity

theorem eta_three_halves_eq_eta_mul_sqrt
    {eta : ℝ} (heta : 0 ≤ eta) :
    eta ^ (3 / 2 : ℝ) = eta * Real.sqrt eta := by
  rw [eta_three_halves_eq_mul_sqrt heta, Real.sqrt_eq_rpow]

theorem pintzDensityLambda_mul_eta
    {eta T : ℝ} (heta : 0 < eta) :
    pintzDensityLambda eta T * eta =
      pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ) * Real.log T +
        pintzDensityLogReserve * Real.log (Real.log T) +
        pintzMobiusLambdaThreshold * eta := by
  rw [eta_three_halves_eq_eta_mul_sqrt heta.le]
  unfold pintzDensityLambda
  field_simp [heta.ne']

theorem pintzMobiusLambdaThreshold_pos :
    0 < pintzMobiusLambdaThreshold :=
  lt_of_lt_of_le (by norm_num) pintzMobiusLambdaThreshold_ge_eight

theorem pintzDensityLambda_ge_threshold
    {eta T : ℝ} (heta : 0 ≤ eta)
    (hT : Real.exp 1 ≤ T) :
    pintzMobiusLambdaThreshold ≤ pintzDensityLambda eta T := by
  have hlogT : 0 ≤ Real.log T := by
    exact Real.log_nonneg ((by
      have : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
      exact this.trans hT))
  have hloglogT : 0 ≤ Real.log (Real.log T) := by
    have hlogOne : 1 ≤ Real.log T := by
      simpa only [Real.log_exp] using
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
          ((Real.exp_pos 1).trans_le hT) hT
    exact Real.log_nonneg hlogOne
  unfold pintzDensityLambda
  have hfirst : 0 ≤
      pintzDensityLambdaCoefficient * Real.sqrt eta * Real.log T := by
    exact mul_nonneg
      (mul_nonneg pintzDensityLambdaCoefficient_pos.le (Real.sqrt_nonneg eta))
      hlogT
  have hsecond : 0 ≤
      pintzDensityLogReserve * Real.log (Real.log T) / eta := by
    exact div_nonneg (mul_nonneg pintzDensityLogReserve_pos.le hloglogT) heta
  linarith

theorem pintzDensityLambda_pos
    {eta T : ℝ} (heta : 0 ≤ eta)
    (hT : Real.exp 1 ≤ T) :
    0 < pintzDensityLambda eta T :=
  pintzMobiusLambdaThreshold_pos.trans_le
    (pintzDensityLambda_ge_threshold heta hT)

theorem pintzDensitySeparation_ge_three
    {eta T : ℝ} (hT : Real.exp 1 ≤ T) :
    3 ≤ pintzDensitySeparation eta T := by
  have hTone : (1 : ℝ) ≤ T :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hTone
  unfold pintzDensitySeparation
  exact le_add_of_nonneg_right (mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans hTone) _)
    (Real.rpow_nonneg hlogT _))

theorem pintzDensitySeparation_pos
    {eta T : ℝ} (hT : Real.exp 1 ≤ T) :
    0 < pintzDensitySeparation eta T :=
  lt_of_lt_of_le (by norm_num) (pintzDensitySeparation_ge_three hT)

#print axioms pintzDensityLambda_mul_eta
#print axioms pintzDensityLambda_ge_threshold
#print axioms pintzDensitySeparation_ge_three

end

end GafniTao
