import GafniTao.PintzDetectorLower

/-!
# A division-safe lower envelope for the detected value

This file keeps the numerator and denominator estimates separate before
forming their quotient.  That avoids hiding positivity assumptions when the
finite density inequality is divided by the square of the detected value.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzDetectorNumeratorLower
    (c eta T : ℝ) : ℝ :=
  (c ^ 2 / Real.log T ^ 2) *
    (Real.exp (-1 / 2) *
      (T ^ (2 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (2 * pintzDensityLogReserve)))

noncomputable def pintzDetectorDenominatorUpper
    (c eta T : ℝ) : ℝ :=
  (32 * (pintzDensityLambdaLogCoefficient c * Real.log T ^ 2) *
    (pintzZetaEnvelopeCoefficient *
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
      Real.log T)) ^ 2

noncomputable def pintzDetectorSquareLower
    (c eta T : ℝ) : ℝ :=
  pintzDetectorNumeratorLower c eta T /
    pintzDetectorDenominatorUpper c eta T

theorem pintzDetectorNumeratorLower_nonneg
    {c eta T : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T) :
    0 ≤ pintzDetectorNumeratorLower c eta T := by
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  unfold pintzDetectorNumeratorLower
  exact mul_nonneg
    (div_nonneg (sq_nonneg c) (sq_nonneg (Real.log T)))
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg hTpos.le _)
        (Real.rpow_nonneg hlogPos.le _)))

theorem pintzDetectorDenominatorUpper_pos
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    0 < pintzDetectorDenominatorUpper c eta T := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  unfold pintzDetectorDenominatorUpper
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  have hZ := pintzZetaEnvelopeCoefficient_pos
  positivity

theorem pintzDetectedLowerBound_sq_eq
    {eta lambda T : ℝ} (heta : 0 < eta) (hlambda : 0 < lambda)
    (hZ : 0 < pintzPhysicalZetaMajorant eta T) :
    pintzDetectedLowerBound eta lambda T ^ 2 =
      (eta ^ 2 * Real.exp (2 * (lambda * eta - 1 / 4))) /
        (32 * lambda * pintzPhysicalZetaMajorant eta T) ^ 2 := by
  unfold pintzDetectedLowerBound
  rw [div_pow]
  field_simp [heta.ne', hlambda.ne', hZ.ne', Real.exp_ne_zero]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  rw [show (1 - lambda * eta * 4) / 4 +
      (1 - lambda * eta * 4) / 4 +
      2 * (lambda * eta * 4 - 1) / 4 = 0 by ring]
  exact Real.exp_zero.symm

theorem pintzDetectorNumeratorLower_le
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzDetectorNumeratorLower c eta T ≤
      eta ^ 2 *
        Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4)) := by
  have hetaSq := pintz_eta_sq_lower hc hT hetaAbove
  have hExp := pintz_exp_shift_lower heta hT
  have hleftNonneg : 0 ≤ c ^ 2 / Real.log T ^ 2 := by positivity
  have hrightNonneg : 0 ≤
      Real.exp (-1 / 2) *
        (T ^ (2 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (2 * pintzDensityLogReserve)) := by
    have hlog : 0 ≤ Real.log T := by
      have hDpos := vinogradovKorobovDenominator_pos hT
      have hDle := vinogradovKorobovDenominator_le_log hT
      linarith
    have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg hTpos.le _)
        (Real.rpow_nonneg hlog _))
  unfold pintzDetectorNumeratorLower
  exact mul_le_mul hetaSq hExp hrightNonneg (sq_nonneg eta)

theorem pintzDetectedDenominator_le
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (32 * pintzDensityLambda eta T *
        pintzPhysicalZetaMajorant eta T) ^ 2 ≤
      pintzDetectorDenominatorUpper c eta T := by
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hT hetaAbove
  have hZ := pintzPhysicalZetaMajorant_le_power_log heta.le hT
  have hExpOne : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr
      (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
  have hlambdaNonneg : 0 ≤ pintzDensityLambda eta T :=
    (pintzDensityLambda_pos heta.le hExpOne).le
  have hZnonneg : 0 ≤ pintzPhysicalZetaMajorant eta T := by
    exact (pintzPhysicalZetaMajorant_pos (eta := eta)
      (by
        have : (1 : ℝ) ≤ T :=
          (Real.one_le_exp (Real.exp_pos 1).le).trans hT
        linarith)).le
  have hLnonneg : 0 ≤
      pintzDensityLambdaLogCoefficient c * Real.log T ^ 2 :=
    mul_nonneg (pintzDensityLambdaLogCoefficient_pos hc).le (sq_nonneg _)
  have hZU : 0 ≤ pintzZetaEnvelopeCoefficient *
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
      Real.log T := by
    have hlog : 0 ≤ Real.log T := by
      have hDpos := vinogradovKorobovDenominator_pos hT
      have hDle := vinogradovKorobovDenominator_le_log hT
      linarith
    have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
    exact mul_nonneg
      (mul_nonneg pintzZetaEnvelopeCoefficient_pos.le
        (Real.rpow_nonneg hTpos.le _)) hlog
  have hbase :
      32 * pintzDensityLambda eta T * pintzPhysicalZetaMajorant eta T ≤
        32 * (pintzDensityLambdaLogCoefficient c * Real.log T ^ 2) *
          (pintzZetaEnvelopeCoefficient *
            T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
            Real.log T) := by gcongr
  unfold pintzDetectorDenominatorUpper
  exact (sq_le_sq₀
    (mul_nonneg (mul_nonneg (by norm_num) hlambdaNonneg) hZnonneg)
    (mul_nonneg (mul_nonneg (by norm_num) hLnonneg) hZU)).2 hbase

theorem pintzDetectorSquareLower_le_detected
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzDetectorSquareLower c eta T ≤
      pintzDetectedLowerBound eta (pintzDensityLambda eta T) T ^ 2 := by
  have hNum := pintzDetectorNumeratorLower_le hc heta hT hetaAbove
  have hDen := pintzDetectedDenominator_le hc heta hetaUpper hT hetaAbove
  have hDenPos := pintzDetectorDenominatorUpper_pos (eta := eta) hc hT
  have hlambdaPos : 0 < pintzDensityLambda eta T := by
    exact pintzDensityLambda_pos heta.le
      ((Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT)
  have hZpos : 0 < pintzPhysicalZetaMajorant eta T := by
    apply pintzPhysicalZetaMajorant_pos
    have : (1 : ℝ) ≤ T :=
      (Real.one_le_exp (Real.exp_pos 1).le).trans hT
    linarith
  have hActualDenPos : 0 <
      (32 * pintzDensityLambda eta T *
        pintzPhysicalZetaMajorant eta T) ^ 2 := by positivity
  unfold pintzDetectorSquareLower
  rw [pintzDetectedLowerBound_sq_eq heta hlambdaPos hZpos]
  have hActualNumNonneg : 0 ≤ eta ^ 2 *
      Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4)) := by
    positivity
  calc
    pintzDetectorNumeratorLower c eta T /
        pintzDetectorDenominatorUpper c eta T ≤
      (eta ^ 2 *
        Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4))) /
        pintzDetectorDenominatorUpper c eta T :=
      div_le_div_of_nonneg_right hNum hDenPos.le
    _ ≤ (eta ^ 2 *
        Real.exp (2 * (pintzDensityLambda eta T * eta - 1 / 4))) /
          (32 * pintzDensityLambda eta T *
            pintzPhysicalZetaMajorant eta T) ^ 2 :=
      div_le_div_of_nonneg_left hActualNumNonneg hActualDenPos hDen

#print axioms pintzDetectedLowerBound_sq_eq
#print axioms pintzDetectorSquareLower_le_detected

end

end GafniTao
