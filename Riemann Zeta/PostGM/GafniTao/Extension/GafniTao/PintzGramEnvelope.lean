import GafniTao.PintzDetectorEnvelope

/-!
# Power--log envelope for the corrected Gram core

The part of the corrected Gram majorant independent of the separation is
bounded here with the literal Ford exponent.  The terminal dyadic shells are
left as a separate reciprocal-`G` term.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzGramCore (eta T : ℝ) : ℝ :=
  1 + fordQualitativeCoefficient *
    ((4 * T) ^ (fordSourceB 3000000 *
        (4 * eta) ^ (3 / 2 : ℝ)) *
      (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (4 * T) ^ (2 / 3 : ℝ)))

noncomputable def pintzGramTerminalCoefficient
    (eta lambda : ℝ) : ℝ :=
  (Nat.clog 2 (pintzMobiusCutoff lambda) : ℝ) *
    (6 * Real.pi * (pintzMobiusCutoff lambda : ℝ) ^ (4 * eta))

noncomputable def pintzGramEnvelopeCoefficient : ℝ :=
  1 + fordQualitativeCoefficient *
    (1 + 2 * (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ)))

theorem pintzGramEnvelopeCoefficient_pos :
    0 < pintzGramEnvelopeCoefficient := by
  unfold pintzGramEnvelopeCoefficient
  have hF := fordQualitativeCoefficient_nonneg
  positivity

theorem pintzCorrectedPhysicalGramMajorant_eq
    {eta lambda T G : ℝ} (hG : G ≠ 0) :
    pintzCorrectedPhysicalGramMajorant eta lambda T G =
      pintzGramCore eta T + pintzGramTerminalCoefficient eta lambda / G := by
  unfold pintzCorrectedPhysicalGramMajorant
  unfold pintzCorrectedUniformPartialZetaEnvelope
  unfold pintzGramCore pintzGramTerminalCoefficient
  rw [show 1 - (1 - 4 * eta) = 4 * eta by ring]
  field_simp [hG]

theorem log_four_mul_le_two_log
    {T : ℝ} (hT : 4 ≤ T) :
    Real.log (4 * T) ≤ 2 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlogFour : Real.log 4 ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne']
  linarith

theorem log_four_mul_rpow_two_thirds_le_two_log
    {T : ℝ} (hT : 4 ≤ T) :
    Real.log (4 * T) ^ (2 / 3 : ℝ) ≤ 2 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlogOne : 1 ≤ Real.log T := by
    have he : Real.exp 1 ≤ 4 := by
      linarith [Real.exp_one_lt_three]
    exact (Real.le_log_iff_exp_le hTpos).2 (he.trans hT)
  have hlogFourNonneg : 0 ≤ Real.log (4 * T) := by
    apply Real.log_nonneg
    nlinarith
  have hmono := Real.rpow_le_rpow hlogFourNonneg
    (log_four_mul_le_two_log hT) (by norm_num : (0 : ℝ) ≤ 2 / 3)
  exact hmono.trans
    (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))

theorem pintzGramCore_le_power_log
    {eta T : ℝ} (heta : 0 ≤ eta) (hT : 4 ≤ T) :
    pintzGramCore eta T ≤
      pintzGramEnvelopeCoefficient *
        T ^ (16 * fordSourceB 3000000 *
          eta ^ (3 / 2 : ℝ)) * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hlogOne : 1 ≤ Real.log T := by
    have he : Real.exp 1 ≤ 4 := by
      linarith [Real.exp_one_lt_three]
    exact (Real.le_log_iff_exp_le hTpos).2 (he.trans hT)
  have hB : 0 ≤ fordSourceB 3000000 :=
    (by linarith [four_le_fordSourceB_three_million])
  have hq : 0 ≤ eta ^ (3 / 2 : ℝ) := Real.rpow_nonneg heta _
  have hFourT : 4 * T ≤ T ^ (2 : ℕ) := by nlinarith
  have hpower :
      (4 * T) ^ (fordSourceB 3000000 * (4 * eta) ^ (3 / 2 : ℝ)) ≤
        T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) := by
    rw [four_mul_rpow_three_halves heta]
    calc
      (4 * T) ^ (fordSourceB 3000000 *
          (8 * eta ^ (3 / 2 : ℝ))) ≤
        (T ^ (2 : ℕ)) ^ (fordSourceB 3000000 *
          (8 * eta ^ (3 / 2 : ℝ))) := by
            exact Real.rpow_le_rpow (by positivity) hFourT (by positivity)
      _ = T ^ (16 * fordSourceB 3000000 *
          eta ^ (3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ T by linarith)]
        congr 1
        ring
  have hparen :
      1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (4 * T) ^ (2 / 3 : ℝ) ≤
        (1 + 2 * (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ))) *
          Real.log T := by
    have hk : 0 ≤ 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) := by
      positivity
    have hlog := log_four_mul_rpow_two_thirds_le_two_log hT
    nlinarith [mul_le_mul_of_nonneg_left hlog hk]
  have hpowNonneg : 0 ≤ T ^ (16 * fordSourceB 3000000 *
      eta ^ (3 / 2 : ℝ)) := Real.rpow_nonneg hTpos.le _
  have hsourceParenNonneg : 0 ≤
      1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (4 * T) ^ (2 / 3 : ℝ) := by
    have : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by nlinarith)
    positivity
  have hsourcePowerNonneg : 0 ≤
      (4 * T) ^ (fordSourceB 3000000 *
        (4 * eta) ^ (3 / 2 : ℝ)) := by positivity
  unfold pintzGramCore pintzGramEnvelopeCoefficient
  have hmain :
      fordQualitativeCoefficient *
          ((4 * T) ^ (fordSourceB 3000000 *
              (4 * eta) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log (4 * T) ^ (2 / 3 : ℝ))) ≤
        fordQualitativeCoefficient *
          (T ^ (16 * fordSourceB 3000000 *
              eta ^ (3 / 2 : ℝ)) *
            ((1 + 2 * (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ))) *
              Real.log T)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hpower hparen hsourceParenNonneg hpowNonneg)
      fordQualitativeCoefficient_nonneg
  have hpowOne : 1 ≤ T ^ (16 * fordSourceB 3000000 *
      eta ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow hTone
      (mul_nonneg (mul_nonneg (by norm_num) hB) hq)
  have hproductOne : 1 ≤
      T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by nlinarith
  calc
    1 + fordQualitativeCoefficient *
        ((4 * T) ^ (fordSourceB 3000000 *
            (4 * eta) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
            Real.log (4 * T) ^ (2 / 3 : ℝ))) ≤
      1 + fordQualitativeCoefficient *
        (T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) *
          ((1 + 2 * (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ))) *
            Real.log T)) := by
      simpa only [add_comm] using add_le_add_right hmain 1
    _ ≤ (1 + fordQualitativeCoefficient *
          (1 + 2 * (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ)))) *
        T ^ (16 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by
      have hF := fordQualitativeCoefficient_nonneg
      have hK : 0 ≤ 1 + 2 *
          (1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ)) := by positivity
      nlinarith [mul_nonneg hF hK]

theorem pintzGramTerminalCoefficient_nonneg
    {eta lambda : ℝ} :
    0 ≤ pintzGramTerminalCoefficient eta lambda := by
  unfold pintzGramTerminalCoefficient
  positivity

#print axioms pintzCorrectedPhysicalGramMajorant_eq
#print axioms pintzGramCore_le_power_log

end

end GafniTao
