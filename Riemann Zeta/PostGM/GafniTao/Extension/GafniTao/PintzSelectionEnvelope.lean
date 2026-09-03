import GafniTao.PintzAdaptiveEnvelope

/-!
# The displacement-and-separation selection envelope

This file keeps the three integer ceiling losses in `pintzSelectionLoss`
visible.  The resulting logarithmic exponent is `2 + 1 + 260 = 263`:
two powers from the displacement window, one from the local zero count, and
260 from the adaptive separation.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzSelectionEnvelopeCoefficient (c : ℝ) : ℝ :=
  4 * (4 * pintzDensityLambdaLogCoefficient c + 3) *
    (globalLocalZeroLogConstant + 1) *
    (2 * pintzAdaptiveEnvelopeCoefficient c + 3)

theorem pintzSelectionEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzSelectionEnvelopeCoefficient c := by
  unfold pintzSelectionEnvelopeCoefficient
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  have hA := pintzAdaptiveEnvelopeCoefficient_pos hc
  have hZ := globalLocalZeroLogConstant_pos
  positivity

theorem pintz_selectionLoss_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hCoreHeight : pintzCoreAbsorptionHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (pintzSelectionLoss (2 * pintzDensityLambda eta T)
        (pintzAdaptiveSeparation c eta T) T : ℝ) ≤
      pintzSelectionEnvelopeCoefficient c *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (263 : ℝ) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
  have hsqOne : 1 ≤ Real.log T ^ 2 := by nlinarith
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta (by linarith) hT hetaAbove
  have hlambdaPos : 0 < pintzDensityLambda eta T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact pintzDensityLambda_pos heta.le hExp
  have hG := pintz_adaptiveSeparation_le_envelope
    hc heta hetaUpper hT hCoreHeight hetaAbove
  have hGthree := pintzAdaptiveSeparation_ge_three
    (eta := eta) hc hT
  have hceilH :
      (Nat.ceil (2 * pintzDensityLambda eta T) : ℝ) ≤
        2 * pintzDensityLambda eta T + 1 :=
    (Nat.ceil_lt_add_one (by positivity :
      0 ≤ 2 * pintzDensityLambda eta T)).le
  have hfactorH :
      ((2 * Nat.ceil (2 * pintzDensityLambda eta T) + 1 : ℕ) : ℝ) ≤
        (4 * pintzDensityLambdaLogCoefficient c + 3) *
          Real.log T ^ 2 := by
    push_cast
    nlinarith [mul_nonneg
      (pintzDensityLambdaLogCoefficient_pos hc).le
      (sq_nonneg (Real.log T))]
  have hlocalArg : 0 ≤ globalLocalZeroLogConstant * Real.log T :=
    mul_nonneg globalLocalZeroLogConstant_pos.le hlogPos.le
  have hceilLocal :
      (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
        globalLocalZeroLogConstant * Real.log T + 1 :=
    (Nat.ceil_lt_add_one hlocalArg).le
  have hfactorLocal :
      (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
        (globalLocalZeroLogConstant + 1) * Real.log T := by
    nlinarith
  have hceilG :
      (Nat.ceil (pintzAdaptiveSeparation c eta T) : ℝ) ≤
        pintzAdaptiveSeparation c eta T + 1 :=
    (Nat.ceil_lt_add_one (by linarith :
      0 ≤ pintzAdaptiveSeparation c eta T)).le
  have hTone : 1 ≤ T := by
    have hone : 1 ≤ Real.exp (Real.exp 1) :=
      Real.one_le_exp (Real.exp_pos 1).le
    exact hone.trans hT
  have hpowerOne : 1 ≤ T ^ (4 * pintzDensityLambdaCoefficient *
      eta ^ (3 / 2 : ℝ)) := by
    apply Real.one_le_rpow hTone
    exact mul_nonneg
      (mul_nonneg (by norm_num) pintzDensityLambdaCoefficient_pos.le)
      (Real.rpow_nonneg heta.le _)
  have hlog260One : 1 ≤ Real.log T ^ (260 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hscaleOne : 1 ≤
      T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpowerOne)
      (sub_nonneg.mpr hlog260One)]
  have hfactorG :
      ((2 * Nat.ceil (pintzAdaptiveSeparation c eta T) + 1 : ℕ) : ℝ) ≤
        (2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
          (T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (260 : ℝ)) := by
    push_cast
    nlinarith [mul_nonneg
      (pintzAdaptiveEnvelopeCoefficient_pos hc).le
      (by positivity : 0 ≤
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (260 : ℝ))]
  have hfactorH' :
      2 * (Nat.ceil (2 * pintzDensityLambda eta T) : ℝ) + 1 ≤
        (4 * pintzDensityLambdaLogCoefficient c + 3) *
          Real.log T ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfactorH
    exact hfactorH
  have hfactorG' :
      2 * (Nat.ceil (pintzAdaptiveSeparation c eta T) : ℝ) + 1 ≤
        (2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
          (T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (260 : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfactorG
    exact hfactorG
  have hfactorHNonneg : 0 ≤
      (4 * pintzDensityLambdaLogCoefficient c + 3) * Real.log T ^ 2 :=
    mul_nonneg (by linarith [pintzDensityLambdaLogCoefficient_pos hc])
      (sq_nonneg _)
  have hfactorLocalNonneg : 0 ≤
      (globalLocalZeroLogConstant + 1) * Real.log T :=
    mul_nonneg (by linarith [globalLocalZeroLogConstant_pos]) hlogPos.le
  have hlogCombine :
      Real.log T ^ (2 : ℕ) * Real.log T *
          Real.log T ^ (260 : ℝ) =
        Real.log T ^ (263 : ℝ) := by
    rw [show Real.log T ^ (260 : ℝ) = Real.log T ^ (260 : ℕ) by
      exact Real.rpow_natCast _ 260]
    rw [show Real.log T ^ (263 : ℝ) = Real.log T ^ (263 : ℕ) by
      exact Real.rpow_natCast _ 263]
    ring
  unfold pintzSelectionLoss pintzSelectionEnvelopeCoefficient
  push_cast
  calc
    2 * ((2 * (Nat.ceil (2 * pintzDensityLambda eta T) : ℝ) + 1) *
          (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ)) *
        (2 * (2 * (Nat.ceil (pintzAdaptiveSeparation c eta T) : ℝ) + 1)) ≤
      2 * (((4 * pintzDensityLambdaLogCoefficient c + 3) *
            Real.log T ^ 2) *
          ((globalLocalZeroLogConstant + 1) * Real.log T)) *
        (2 * ((2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
          (T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (260 : ℝ)))) := by gcongr
    _ = 4 * (4 * pintzDensityLambdaLogCoefficient c + 3) *
        (globalLocalZeroLogConstant + 1) *
        (2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (263 : ℝ) := by
      rw [show
        2 * (((4 * pintzDensityLambdaLogCoefficient c + 3) *
              Real.log T ^ 2) *
            ((globalLocalZeroLogConstant + 1) * Real.log T)) *
          (2 * ((2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
            (T ^ (4 * pintzDensityLambdaCoefficient *
                eta ^ (3 / 2 : ℝ)) * Real.log T ^ (260 : ℝ)))) =
        4 * (4 * pintzDensityLambdaLogCoefficient c + 3) *
          (globalLocalZeroLogConstant + 1) *
          (2 * pintzAdaptiveEnvelopeCoefficient c + 3) *
          T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
          (Real.log T ^ (2 : ℕ) * Real.log T *
            Real.log T ^ (260 : ℝ)) by ring]
      rw [hlogCombine]

#print axioms pintz_selectionLoss_le_envelope

end

end GafniTao
