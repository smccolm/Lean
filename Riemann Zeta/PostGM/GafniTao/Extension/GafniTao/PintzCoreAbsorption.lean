import GafniTao.PintzGramEnvelope

/-!
# Uniform absorption of the Ford-controlled Gram core

The detector's logarithmic reserve leaves 117 powers of `log T` after all
cutoff, zeta-envelope, harmonic, and denominator losses.  This file spends
those powers to absorb the separation-independent Ford term uniformly above
the Vinogradov--Korobov boundary.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzCoreAbsorptionCoefficient (c : ℝ) : ℝ :=
  (4 * (pintzDensityLambdaLogCoefficient c + 5) *
    pintzGramEnvelopeCoefficient *
    (32 * pintzDensityLambdaLogCoefficient c *
      pintzZetaEnvelopeCoefficient) ^ 2) /
    (c ^ 2 * Real.exp (-1 / 2))

noncomputable def pintzCoreAbsorptionHeight (c : ℝ) : ℝ :=
  Real.exp (max 4 (pintzCoreAbsorptionCoefficient c))

theorem pintzCoreAbsorptionCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzCoreAbsorptionCoefficient c := by
  unfold pintzCoreAbsorptionCoefficient
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  have hG := pintzGramEnvelopeCoefficient_pos
  have hZ := pintzZetaEnvelopeCoefficient_pos
  positivity

theorem pintz_core_absorption_log_budget
    {c T : ℝ}
    (hT : pintzCoreAbsorptionHeight c ≤ T) :
    pintzCoreAbsorptionCoefficient c ≤ Real.log T ^ (117 : ℝ) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : max 4 (pintzCoreAbsorptionCoefficient c) ≤
      Real.log T := by
    simpa only [pintzCoreAbsorptionHeight, Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos _) hTpos hT
  have hlogOne : 1 ≤ Real.log T := by
    linarith [le_max_left (4 : ℝ) (pintzCoreAbsorptionCoefficient c)]
  have hself : Real.log T ≤ Real.log T ^ (117 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlogOne
        (by norm_num : (1 : ℝ) ≤ 117)
  exact (le_max_right (4 : ℝ) _).trans hlogLower |>.trans hself

theorem pintz_core_power_exponent_le :
    16 * fordSourceB 3000000 +
        2 * pintzZetaExponentCoefficient ≤
      2 * pintzDensityLambdaCoefficient := by
  unfold pintzZetaExponentCoefficient pintzDensityLambdaCoefficient
  have hB := four_le_fordSourceB_three_million
  nlinarith

theorem pintz_core_absorbed_by_detector_square
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hTbase : Real.exp (Real.exp 1) ≤ T)
    (hTabsorb : pintzCoreAbsorptionHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    4 * (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) *
        pintzGramCore eta T ≤
      pintzDetectorSquareLower c eta T := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hTbase
  have hTfour : (4 : ℝ) ≤ T := by
    have hExpFour : (4 : ℝ) ≤ Real.exp (Real.exp 1) := by
      have hExpOne : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hExpTwo : (4 : ℝ) ≤ Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_gt_d9]
      exact hExpTwo.trans (Real.exp_le_exp.mpr hExpOne)
    exact hExpFour.trans hTbase
  have hlogOne : 1 ≤ Real.log T := by
    have hTExp : Real.exp 1 ≤ T := by
      exact (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hTbase
    exact (Real.le_log_iff_exp_le hTpos).2 hTExp
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hTbase hetaAbove
  have hlambdaLower : -3 ≤ pintzDensityLambda eta T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hTbase
    linarith [pintzDensityLambda_pos heta.le hExp]
  have hHraw := pintzMobiusCutoff_harmonic_le hlambdaLower
  have hH : (harmonic (pintzMobiusCutoff
      (pintzDensityLambda eta T)) : ℝ) ≤
      (pintzDensityLambdaLogCoefficient c + 5) * Real.log T ^ 2 := by
    have hfive : (5 : ℝ) ≤ 5 * Real.log T ^ 2 := by
      nlinarith [sq_nonneg (Real.log T - 1)]
    calc
      _ ≤ pintzDensityLambda eta T + 5 := hHraw
      _ ≤ pintzDensityLambdaLogCoefficient c * Real.log T ^ 2 +
          5 * Real.log T ^ 2 := add_le_add hlambda hfive
      _ = _ := by ring
  have hcore := pintzGramCore_le_power_log heta.le hTfour
  have hDenPos := pintzDetectorDenominatorUpper_pos (eta := eta) hc hTbase
  apply (le_div_iff₀ hDenPos).2
  unfold pintzDetectorNumeratorLower pintzDetectorDenominatorUpper
  have hq : 0 ≤ eta ^ (3 / 2 : ℝ) := Real.rpow_nonneg heta.le _
  have hpowerExponent :
      (16 * fordSourceB 3000000 + 2 * pintzZetaExponentCoefficient) *
          eta ^ (3 / 2 : ℝ) ≤
        (2 * pintzDensityLambdaCoefficient) *
          eta ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right pintz_core_power_exponent_le hq
  have hTone : (1 : ℝ) ≤ T := by linarith
  have hpower :
      T ^ ((16 * fordSourceB 3000000 +
          2 * pintzZetaExponentCoefficient) * eta ^ (3 / 2 : ℝ)) ≤
        T ^ ((2 * pintzDensityLambdaCoefficient) *
          eta ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hTone hpowerExponent
  have hlogBudget := pintz_core_absorption_log_budget hTabsorb
  have hCoeffEq :
      4 * (pintzDensityLambdaLogCoefficient c + 5) *
          pintzGramEnvelopeCoefficient *
          (32 * pintzDensityLambdaLogCoefficient c *
            pintzZetaEnvelopeCoefficient) ^ 2 ≤
        (c ^ 2 * Real.exp (-1 / 2)) * Real.log T ^ (117 : ℝ) := by
    have hden : 0 < c ^ 2 * Real.exp (-1 / 2) := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hden).mp hlogBudget
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
  have hcoreNonneg : 0 ≤ pintzGramCore eta T := by
    unfold pintzGramCore
    have hlog : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by nlinarith)
    have hpow : 0 ≤ (4 * T) ^ (fordSourceB 3000000 *
        (4 * eta) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg (by nlinarith) _
    have hparen : 0 ≤
        1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (4 * T) ^ (2 / 3 : ℝ) := by positivity
    exact add_nonneg zero_le_one
      (mul_nonneg fordQualitativeCoefficient_nonneg
        (mul_nonneg hpow hparen))
  have hHUpperNonneg : 0 ≤
      4 * ((pintzDensityLambdaLogCoefficient c + 5) *
        Real.log T ^ 2) := by
    have hL := pintzDensityLambdaLogCoefficient_pos hc
    positivity
  have hleftBound :
      4 * (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) *
          pintzGramCore eta T *
          (32 * (pintzDensityLambdaLogCoefficient c * Real.log T ^ 2) *
            (pintzZetaEnvelopeCoefficient *
              T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
              Real.log T)) ^ 2 ≤
        4 * ((pintzDensityLambdaLogCoefficient c + 5) *
            Real.log T ^ 2) *
          (pintzGramEnvelopeCoefficient *
            T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) *
            Real.log T) *
          (32 * (pintzDensityLambdaLogCoefficient c * Real.log T ^ 2) *
            (pintzZetaEnvelopeCoefficient *
              T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
              Real.log T)) ^ 2 := by
    gcongr
  calc
    4 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        pintzGramCore eta T *
        (32 * (pintzDensityLambdaLogCoefficient c * Real.log T ^ 2) *
          (pintzZetaEnvelopeCoefficient *
            T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
            Real.log T)) ^ 2 ≤ _ := hleftBound
    _ = (4 * (pintzDensityLambdaLogCoefficient c + 5) *
          pintzGramEnvelopeCoefficient *
          (32 * pintzDensityLambdaLogCoefficient c *
            pintzZetaEnvelopeCoefficient) ^ 2) *
        T ^ ((16 * fordSourceB 3000000 +
          2 * pintzZetaExponentCoefficient) * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (9 : ℝ) := by
      rw [show Real.log T ^ (9 : ℝ) = Real.log T ^ (9 : ℕ) by
        exact Real.rpow_natCast _ _]
      rw [show T ^ ((16 * fordSourceB 3000000 +
          2 * pintzZetaExponentCoefficient) * eta ^ (3 / 2 : ℝ)) =
        T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) *
          (T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ))) ^ 2 by
          rw [pow_two, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          congr 1
          ring]
      ring
    _ ≤ ((c ^ 2 * Real.exp (-1 / 2)) * Real.log T ^ (117 : ℝ)) *
        T ^ ((2 * pintzDensityLambdaCoefficient) *
          eta ^ (3 / 2 : ℝ)) * Real.log T ^ (9 : ℝ) := by
      gcongr
    _ = (c ^ 2 * Real.exp (-1 / 2)) *
        T ^ ((2 * pintzDensityLambdaCoefficient) *
          eta ^ (3 / 2 : ℝ)) * Real.log T ^ (126 : ℝ) := by
      rw [show Real.log T ^ (126 : ℝ) =
          Real.log T ^ (117 : ℝ) * Real.log T ^ (9 : ℝ) by
        rw [← Real.rpow_add hlogPos]
        norm_num]
      ring
    _ = (c ^ 2 / Real.log T ^ 2) *
        (Real.exp (-1 / 2) *
          (T ^ (2 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (2 * pintzDensityLogReserve))) := by
      unfold pintzDensityLogReserve
      rw [show Real.log T ^ (2 : ℕ) = Real.log T ^ (2 : ℝ) by
        exact (Real.rpow_natCast _ _).symm]
      field_simp [hlogPos.ne']
      rw [← Real.rpow_add hlogPos]
      norm_num

#print axioms pintz_core_absorption_log_budget
#print axioms pintz_core_absorbed_by_detector_square

end

end GafniTao
