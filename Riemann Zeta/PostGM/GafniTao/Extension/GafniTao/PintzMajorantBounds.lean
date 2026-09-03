import GafniTao.PintzVKScale

/-!
# Power--log envelopes for Pintz's physical zeta majorant

The contour argument uses a three-piece zeta estimate.  This file packages
that literal sum into a single fixed-coefficient power--log bound without
changing its `eta^(3/2)` exponent.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintzZetaExponentCoefficient : ℝ :=
  16 * fordSourceB 3000000

noncomputable def pintzZetaEnvelopeCoefficient : ℝ :=
  1 + 2 * fordQualitativeGlobalCoefficient + 2 * pintzLogZetaConstant +
    hughesYoungZetaHalfPlaneMajorant

theorem pintzZetaExponentCoefficient_pos :
    0 < pintzZetaExponentCoefficient := by
  unfold pintzZetaExponentCoefficient
  exact mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num)
    four_le_fordSourceB_three_million)

theorem pintzZetaEnvelopeCoefficient_pos :
    0 < pintzZetaEnvelopeCoefficient := by
  unfold pintzZetaEnvelopeCoefficient
  have hA := fordQualitativeGlobalCoefficient_nonneg
  have hC := pintzLogZetaConstant_pos.le
  have hH := hughesYoungZetaHalfPlaneMajorant_nonneg
  linarith

theorem four_mul_rpow_three_halves
    {eta : ℝ} (heta : 0 ≤ eta) :
    (4 * eta) ^ (3 / 2 : ℝ) = 8 * eta ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) heta]
  norm_num [Real.rpow_def_of_pos]

theorem two_mul_eta_rpow_three_halves_le
    {eta : ℝ} (heta : 0 ≤ eta) :
    (2 * eta) ^ (3 / 2 : ℝ) ≤ 8 * eta ^ (3 / 2 : ℝ) := by
  calc
    (2 * eta) ^ (3 / 2 : ℝ) ≤ (4 * eta) ^ (3 / 2 : ℝ) := by
      apply Real.rpow_le_rpow (mul_nonneg (by norm_num) heta)
      · nlinarith
      · norm_num
    _ = 8 * eta ^ (3 / 2 : ℝ) := four_mul_rpow_three_halves heta

theorem log_two_mul_le_two_log
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    Real.log (2 * T) ≤ 2 * Real.log T := by
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogTOne : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hTpos hT
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  linarith [Real.log_two_lt_d9]

theorem log_two_mul_rpow_two_thirds_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    Real.log (2 * T) ^ (2 / 3 : ℝ) ≤ 2 * Real.log T := by
  have hlogTOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hTpos hT
  have hlogTwoTNonneg : 0 ≤ Real.log (2 * T) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ T :=
      (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hT
    nlinarith
  have hmono := Real.rpow_le_rpow hlogTwoTNonneg
    (log_two_mul_le_two_log hT) (by norm_num : (0 : ℝ) ≤ 2 / 3)
  exact hmono.trans (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))

theorem pintzPhysicalZetaMajorant_le_power_log
    {eta T : ℝ} (heta : 0 ≤ eta)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    pintzPhysicalZetaMajorant eta T ≤
      pintzZetaEnvelopeCoefficient *
        T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by
  have hTExp : Real.exp 1 ≤ T := by
    have hExp : Real.exp 1 ≤ Real.exp (Real.exp 1) :=
      Real.exp_le_exp.mpr (by
        exact (Real.one_lt_exp_iff.mpr zero_lt_one).le)
    exact hExp.trans hT
  have hTOne : (1 : ℝ) ≤ T :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hTExp
  have hlogOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := zero_lt_one.trans_le hTOne
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hTpos hTExp
  have hq : 0 ≤ eta ^ (3 / 2 : ℝ) := Real.rpow_nonneg heta _
  have hB : 0 ≤ fordSourceB 3000000 :=
    le_trans (by norm_num) four_le_fordSourceB_three_million
  have hExpNonneg : 0 ≤
      pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ) := by
    exact mul_nonneg pintzZetaExponentCoefficient_pos.le hq
  have hPowOne : 1 ≤
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow hTOne hExpNonneg
  have hetaExponent :
      fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ) ≤
        8 * fordSourceB 3000000 * eta ^ (3 / 2 : ℝ) := by
    nlinarith [two_mul_eta_rpow_three_halves_le heta]
  have hTwoT : 2 * T ≤ T ^ (2 : ℕ) := by
    have hExpTwo : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hTTwo : (2 : ℝ) ≤ T := hExpTwo.trans hTExp
    nlinarith
  have hPow :
      (2 * T) ^ (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) ≤
        T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) := by
    calc
      (2 * T) ^ (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) ≤
          (T ^ (2 : ℕ)) ^
            (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) := by
        exact Real.rpow_le_rpow (by positivity) hTwoT
          (mul_nonneg hB (Real.rpow_nonneg (mul_nonneg (by norm_num) heta) _))
      _ = T ^ (2 *
            (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hTOne)]
        ring_nf
      _ ≤ T ^ (pintzZetaExponentCoefficient *
            eta ^ (3 / 2 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hTOne
        unfold pintzZetaExponentCoefficient
        linarith
  have hlogPower := log_two_mul_rpow_two_thirds_le hTExp
  have hlog := log_two_mul_le_two_log hTExp
  have hlogTwoPowerNonneg :
      0 ≤ Real.log (2 * T) ^ (2 / 3 : ℝ) := by
    have hTwoTOne : (1 : ℝ) ≤ 2 * T := by nlinarith
    exact Real.rpow_nonneg (Real.log_nonneg hTwoTOne) _
  have hPowerNonneg : 0 ≤
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans hTOne) _
  have hlogNonneg : 0 ≤ Real.log T := zero_le_one.trans hlogOne
  unfold pintzPhysicalZetaMajorant pintzHorizontalZetaMajorant
  unfold pintzZetaEnvelopeCoefficient
  have hFord :
      fordQualitativeGlobalCoefficient *
          (2 * T) ^ (fordSourceB 3000000 * (2 * eta) ^ (3 / 2 : ℝ)) *
          Real.log (2 * T) ^ (2 / 3 : ℝ) ≤
        (2 * fordQualitativeGlobalCoefficient) *
          T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.log T := by
    have hA := fordQualitativeGlobalCoefficient_nonneg
    calc
      _ ≤ fordQualitativeGlobalCoefficient *
          T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
          (2 * Real.log T) := by gcongr
      _ = _ := by ring
  have hPNT : pintzLogZetaConstant * Real.log (2 * T) ≤
      (2 * pintzLogZetaConstant) *
        T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by
    have hC := pintzLogZetaConstant_pos.le
    calc
      _ ≤ pintzLogZetaConstant * (2 * Real.log T) := by gcongr
      _ ≤ (2 * pintzLogZetaConstant) *
          T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.log T := by
        nlinarith [mul_nonneg hC hlogNonneg]
  have hOne : (1 : ℝ) ≤
      1 * T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by
    nlinarith
  have hHalfPlane : hughesYoungZetaHalfPlaneMajorant ≤
      hughesYoungZetaHalfPlaneMajorant *
        T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T := by
    have hH := hughesYoungZetaHalfPlaneMajorant_nonneg
    nlinarith
  linarith

#print axioms four_mul_rpow_three_halves
#print axioms pintzPhysicalZetaMajorant_le_power_log

end

end GafniTao
