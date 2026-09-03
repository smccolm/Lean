import GafniTao.PintzCoreAbsorption

/-!
# Complete off-diagonal absorption

The separation is chosen from the literal terminal-shell coefficient and the
proved detector lower envelope.  The Ford-controlled core consumes one half
of the square; the reciprocal-separation term consumes the other half.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzAdaptiveSeparation (c eta T : ℝ) : ℝ :=
  3 +
    4 * (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) *
      pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
      pintzDetectorSquareLower c eta T

theorem pintzDetectorSquareLower_pos
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    0 < pintzDetectorSquareLower c eta T := by
  unfold pintzDetectorSquareLower
  have hDen := pintzDetectorDenominatorUpper_pos (eta := eta) hc hT
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  unfold pintzDetectorNumeratorLower
  apply div_pos
  · exact mul_pos (div_pos (sq_pos_of_pos hc) (sq_pos_of_pos hlogPos))
      (mul_pos (Real.exp_pos _)
        (mul_pos (Real.rpow_pos_of_pos hTpos _)
          (Real.rpow_pos_of_pos hlogPos _)))
  · exact hDen

theorem pintzAdaptiveSeparation_ge_three
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    3 ≤ pintzAdaptiveSeparation c eta T := by
  have hS := pintzDetectorSquareLower_pos (eta := eta) hc hT
  have hH : 0 ≤
      (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hterm := pintzGramTerminalCoefficient_nonneg
    (eta := eta) (lambda := pintzDensityLambda eta T)
  unfold pintzAdaptiveSeparation
  exact le_add_of_nonneg_right (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hH) hterm) hS.le)

theorem pintz_terminal_absorbed_by_adaptive_separation
    {c eta T : ℝ} (hc : 0 < c)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    2 * (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) *
        (pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
          pintzAdaptiveSeparation c eta T) ≤
      pintzDetectorSquareLower c eta T / 2 := by
  let H : ℝ := harmonic
    (pintzMobiusCutoff (pintzDensityLambda eta T))
  let R : ℝ := pintzGramTerminalCoefficient eta
    (pintzDensityLambda eta T)
  let S : ℝ := pintzDetectorSquareLower c eta T
  have hS : 0 < S := pintzDetectorSquareLower_pos (eta := eta) hc hT
  have hH : 0 ≤ H := by
    dsimp [H]
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact pintzGramTerminalCoefficient_nonneg
  have hG : 0 < pintzAdaptiveSeparation c eta T :=
    lt_of_lt_of_le (by norm_num)
      (pintzAdaptiveSeparation_ge_three (eta := eta) hc hT)
  have hGlarge : 4 * H * R / S ≤
      pintzAdaptiveSeparation c eta T := by
    unfold pintzAdaptiveSeparation
    dsimp only [H, R, S]
    linarith
  have hmul : 4 * H * R ≤
      pintzAdaptiveSeparation c eta T * S := by
    exact (div_le_iff₀ hS).mp hGlarge
  dsimp only [H, R, S] at hmul ⊢
  rw [show 2 * (harmonic (pintzMobiusCutoff
      (pintzDensityLambda eta T)) : ℝ) *
        (pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
          pintzAdaptiveSeparation c eta T) =
      (2 * (harmonic (pintzMobiusCutoff
        (pintzDensityLambda eta T)) : ℝ) *
        pintzGramTerminalCoefficient eta (pintzDensityLambda eta T)) /
          pintzAdaptiveSeparation c eta T by ring]
  apply (div_le_iff₀ hG).2
  nlinarith

theorem pintz_off_diagonal_absorption
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hTbase : Real.exp (Real.exp 1) ≤ T)
    (hTabsorb : pintzCoreAbsorptionHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    2 * (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) *
        pintzCorrectedPhysicalGramMajorant eta
          (pintzDensityLambda eta T) T
          (pintzAdaptiveSeparation c eta T) ≤
      pintzDetectedLowerBound eta (pintzDensityLambda eta T) T ^ 2 := by
  have hSpos := pintzDetectorSquareLower_pos (eta := eta) hc hTbase
  have hG : 0 < pintzAdaptiveSeparation c eta T :=
    lt_of_lt_of_le (by norm_num)
      (pintzAdaptiveSeparation_ge_three (eta := eta) hc hTbase)
  have hcore := pintz_core_absorbed_by_detector_square
    hc heta hetaUpper hTbase hTabsorb hetaAbove
  have hterminal := pintz_terminal_absorbed_by_adaptive_separation
    (eta := eta) hc hTbase
  have hLower := pintzDetectorSquareLower_le_detected
    hc heta hetaUpper hTbase hetaAbove
  rw [pintzCorrectedPhysicalGramMajorant_eq hG.ne']
  have hH : 0 ≤
      (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  calc
    2 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        (pintzGramCore eta T +
          pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
            pintzAdaptiveSeparation c eta T) =
      (2 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) * pintzGramCore eta T) +
      (2 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        (pintzGramTerminalCoefficient eta (pintzDensityLambda eta T) /
          pintzAdaptiveSeparation c eta T)) := by ring
    _ ≤ pintzDetectorSquareLower c eta T / 2 +
        pintzDetectorSquareLower c eta T / 2 := by
      apply add_le_add
      · nlinarith
      · exact hterminal
    _ = pintzDetectorSquareLower c eta T := by ring
    _ ≤ pintzDetectedLowerBound eta (pintzDensityLambda eta T) T ^ 2 :=
      hLower

#print axioms pintz_terminal_absorbed_by_adaptive_separation
#print axioms pintz_off_diagonal_absorption

end

end GafniTao
