import GafniTao.PintzCutoffPowerEnvelope

/-!
# Harmonic, dyadic, and adaptive-separation envelopes
-/

namespace GafniTao

noncomputable section

noncomputable def pintzHarmonicEnvelopeCoefficient (c : ℝ) : ℝ :=
  pintzDensityLambdaLogCoefficient c + 5

noncomputable def pintzClogEnvelopeCoefficient (c : ℝ) : ℝ :=
  1 + (pintzDensityLambdaLogCoefficient c + 4) / Real.log 2

noncomputable def pintzTerminalEnvelopeCoefficient (c : ℝ) : ℝ :=
  pintzClogEnvelopeCoefficient c * (6 * Real.pi) *
    pintzCutoffPowerCoefficient

noncomputable def pintzAdaptiveEnvelopeCoefficient (c : ℝ) : ℝ :=
  3 + pintzHarmonicEnvelopeCoefficient c *
    pintzTerminalEnvelopeCoefficient c

theorem pintzHarmonicEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzHarmonicEnvelopeCoefficient c := by
  unfold pintzHarmonicEnvelopeCoefficient
  linarith [pintzDensityLambdaLogCoefficient_pos hc]

theorem pintzClogEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzClogEnvelopeCoefficient c := by
  unfold pintzClogEnvelopeCoefficient
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  positivity

theorem pintzTerminalEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzTerminalEnvelopeCoefficient c := by
  unfold pintzTerminalEnvelopeCoefficient
  exact mul_pos (mul_pos (pintzClogEnvelopeCoefficient_pos hc)
    (mul_pos (by norm_num) Real.pi_pos)) pintzCutoffPowerCoefficient_pos

theorem pintzAdaptiveEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzAdaptiveEnvelopeCoefficient c := by
  unfold pintzAdaptiveEnvelopeCoefficient
  exact add_pos_of_pos_of_nonneg (by norm_num)
    (mul_nonneg (pintzHarmonicEnvelopeCoefficient_pos hc).le
      (pintzTerminalEnvelopeCoefficient_pos hc).le)

theorem pintz_harmonic_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) ≤
      pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2 := by
  have hlogOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hT hetaAbove
  have hExp : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr
      (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
  have hlambdaLower : -3 ≤ pintzDensityLambda eta T := by
    linarith [pintzDensityLambda_pos heta.le hExp]
  have hH := pintzMobiusCutoff_harmonic_le hlambdaLower
  unfold pintzHarmonicEnvelopeCoefficient
  nlinarith

theorem pintz_clog_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (Nat.clog 2 (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) ≤
      pintzClogEnvelopeCoefficient c * Real.log T ^ 2 := by
  have hlogOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hT hetaAbove
  have hExp : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr
      (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
  have hlambdaLower : -3 ≤ pintzDensityLambda eta T := by
    linarith [pintzDensityLambda_pos heta.le hExp]
  have hC := pintzMobiusCutoff_clog_le hlambdaLower
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold pintzClogEnvelopeCoefficient
  have hdiv :
      (pintzDensityLambda eta T + 4) / Real.log 2 ≤
        ((pintzDensityLambdaLogCoefficient c + 4) / Real.log 2) *
          Real.log T ^ 2 := by
    have hsq : 1 ≤ Real.log T ^ 2 := by nlinarith
    have hnum : pintzDensityLambda eta T + 4 ≤
        (pintzDensityLambdaLogCoefficient c + 4) * Real.log T ^ 2 := by
      nlinarith [mul_nonneg
        (pintzDensityLambdaLogCoefficient_pos hc).le (sq_nonneg (Real.log T))]
    have hquot := div_le_div_of_nonneg_right hnum hlogTwo.le
    calc
      _ ≤ (pintzDensityLambdaLogCoefficient c + 4) *
          Real.log T ^ 2 / Real.log 2 := hquot
      _ = _ := by ring
  nlinarith

theorem pintz_terminal_coefficient_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) ≤
      pintzTerminalEnvelopeCoefficient c *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (258 : ℝ) := by
  have hclog := pintz_clog_le_envelope hc heta (by linarith) hT hetaAbove
  have hcutoff := pintz_cutoff_rpow_four_eta_le heta hetaUpper hT
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  have hclogUpperNonneg : 0 ≤
      pintzClogEnvelopeCoefficient c * Real.log T ^ 2 :=
    mul_nonneg (pintzClogEnvelopeCoefficient_pos hc).le
      (sq_nonneg (Real.log T))
  have hlogCombine :
      Real.log T ^ (2 : ℕ) *
          Real.log T ^ (4 * pintzDensityLogReserve) =
        Real.log T ^ (258 : ℝ) := by
    rw [show Real.log T ^ (2 : ℕ) = Real.log T ^ (2 : ℝ) by
      exact (Real.rpow_natCast _ _).symm]
    rw [← Real.rpow_add hlogPos]
    unfold pintzDensityLogReserve
    norm_num
  unfold pintzGramTerminalCoefficient pintzTerminalEnvelopeCoefficient
  calc
    (Nat.clog 2 (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) *
        (6 * Real.pi *
          (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
            (4 * eta)) ≤
      (pintzClogEnvelopeCoefficient c * Real.log T ^ 2) *
        (6 * Real.pi *
          (pintzCutoffPowerCoefficient *
            T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (4 * pintzDensityLogReserve))) := by gcongr
    _ = pintzClogEnvelopeCoefficient c * (6 * Real.pi) *
        pintzCutoffPowerCoefficient *
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (258 : ℝ) := by
      rw [show
        (pintzClogEnvelopeCoefficient c * Real.log T ^ 2) *
            (6 * Real.pi *
              (pintzCutoffPowerCoefficient *
                T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) *
                Real.log T ^ (4 * pintzDensityLogReserve))) =
          pintzClogEnvelopeCoefficient c * (6 * Real.pi) *
            pintzCutoffPowerCoefficient *
            T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
            (Real.log T ^ (2 : ℕ) *
              Real.log T ^ (4 * pintzDensityLogReserve)) by ring]
      rw [hlogCombine]

theorem pintz_adaptiveSeparation_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hCoreHeight : pintzCoreAbsorptionHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzAdaptiveSeparation c eta T ≤
      pintzAdaptiveEnvelopeCoefficient c *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
  have hS := four_le_pintzDetectorSquareLower
    hc heta (by linarith) hT hCoreHeight hetaAbove
  have hH := pintz_harmonic_le_envelope hc heta (by linarith) hT hetaAbove
  have hR := pintz_terminal_coefficient_le_envelope
    hc heta hetaUpper hT hetaAbove
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
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
  unfold pintzAdaptiveSeparation
  have hfrac :
      4 * (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) *
          pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
          pintzDetectorSquareLower c eta T ≤
        (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) *
          pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) := by
    have hprod : 0 ≤
        (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) *
          pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) := by
      have hterm := pintzGramTerminalCoefficient_nonneg
        (eta := eta) (lambda := pintzDensityLambda eta T)
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    apply (div_le_iff₀ (by linarith : 0 < pintzDetectorSquareLower c eta T)).2
    nlinarith
  have hproduct :
      (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) ≤
      (pintzHarmonicEnvelopeCoefficient c *
          pintzTerminalEnvelopeCoefficient c) *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) * Real.log T ^ (260 : ℝ) := by
    have htermNonneg : 0 ≤
        pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) :=
      pintzGramTerminalCoefficient_nonneg
    have hHUpperNonneg : 0 ≤
        pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2 :=
      mul_nonneg (pintzHarmonicEnvelopeCoefficient_pos hc).le
        (sq_nonneg (Real.log T))
    have hlogCombine :
        Real.log T ^ (2 : ℕ) * Real.log T ^ (258 : ℝ) =
          Real.log T ^ (260 : ℝ) := by
      rw [show Real.log T ^ (2 : ℕ) = Real.log T ^ (2 : ℝ) by
        exact (Real.rpow_natCast _ _).symm]
      rw [← Real.rpow_add (zero_lt_one.trans_le hlogOne)]
      norm_num
    calc
      _ ≤ (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2) *
          (pintzTerminalEnvelopeCoefficient c *
            T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) * Real.log T ^ (258 : ℝ)) := by
        gcongr
      _ = _ := by
        rw [show
          (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2) *
              (pintzTerminalEnvelopeCoefficient c *
                T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) * Real.log T ^ (258 : ℝ)) =
            (pintzHarmonicEnvelopeCoefficient c *
              pintzTerminalEnvelopeCoefficient c) *
              T ^ (4 * pintzDensityLambdaCoefficient *
                eta ^ (3 / 2 : ℝ)) *
              (Real.log T ^ (2 : ℕ) * Real.log T ^ (258 : ℝ)) by ring]
        rw [hlogCombine]
  unfold pintzAdaptiveEnvelopeCoefficient
  calc
    3 + 4 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
        pintzDetectorSquareLower c eta T ≤
      3 + (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) :=
      by simpa only [add_comm] using add_le_add_right hfrac 3
    _ ≤ 3 + (pintzHarmonicEnvelopeCoefficient c *
          pintzTerminalEnvelopeCoefficient c) *
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
      simpa only [add_comm] using add_le_add_right hproduct 3
    _ ≤ (3 + pintzHarmonicEnvelopeCoefficient c *
          pintzTerminalEnvelopeCoefficient c) *
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
      have hscaleOne : 1 ≤
          T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (260 : ℝ) :=
        by
          nlinarith [mul_nonneg (sub_nonneg.mpr hpowerOne)
            (sub_nonneg.mpr hlog260One)]
      nlinarith [mul_nonneg
        (pintzHarmonicEnvelopeCoefficient_pos hc).le
        (pintzTerminalEnvelopeCoefficient_pos hc).le]

#print axioms pintz_terminal_coefficient_le_envelope
#print axioms pintz_adaptiveSeparation_le_envelope

end

end GafniTao
