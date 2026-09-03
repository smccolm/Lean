import GafniTao.PintzErrorEnvelope

/-!
# Discharge of the corrected Pintz contour error

The `sqrt(eta) log T` part of `lambda` dominates the Ford power in the zeta
window.  The reserve term contributes `(log T)^(-32/eta)`, which uniformly
absorbs all remaining fixed constants and logarithmic factors.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz_error_exponent_le
    {eta T : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ) * Real.log T -
        pintzDensityLambda eta T / 2 ≤
      -32 * Real.log (Real.log T) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTpos hT
  have hlogPos : 0 < Real.log T := (Real.exp_pos 1).trans_le hlogLower
  have hloglogNonneg : 0 ≤ Real.log (Real.log T) := by
    exact Real.log_nonneg ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hlogLower)
  have hsqrtNonneg : 0 ≤ Real.sqrt eta := Real.sqrt_nonneg eta
  have hscaleNonneg : 0 ≤ Real.sqrt eta * Real.log T :=
    mul_nonneg hsqrtNonneg hlogPos.le
  have hB : 4 ≤ fordSourceB 3000000 := four_le_fordSourceB_three_million
  rw [eta_three_halves_eq_eta_mul_sqrt heta.le]
  unfold pintzZetaExponentCoefficient pintzDensityLambda
  unfold pintzDensityLambdaCoefficient pintzDensityLogReserve
  have hthreshold := pintzMobiusLambdaThreshold_pos.le
  have hpower :
      16 * fordSourceB 3000000 * eta *
          (Real.sqrt eta * Real.log T) ≤
        128 * (1 + fordSourceB 3000000) *
          (Real.sqrt eta * Real.log T) := by
    have hcoeff : 16 * fordSourceB 3000000 * eta ≤
        128 * (1 + fordSourceB 3000000) := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoeff hscaleNonneg
  have hreserve : Real.log (Real.log T) ≤
      Real.log (Real.log T) / eta := by
    apply (le_div_iff₀ heta).2
    nlinarith [mul_nonneg hloglogNonneg (by linarith : 0 ≤ 1 - eta)]
  have hassoc :
      16 * fordSourceB 3000000 * (eta * Real.sqrt eta) * Real.log T =
        16 * fordSourceB 3000000 * eta *
          (Real.sqrt eta * Real.log T) := by ring
  rw [hassoc]
  have hfirst :
      16 * fordSourceB 3000000 * eta *
            (Real.sqrt eta * Real.log T) -
          (256 * (1 + fordSourceB 3000000) *
            (Real.sqrt eta * Real.log T)) / 2 ≤ 0 := by
    nlinarith
  have hsecond :
      -(64 * (Real.log (Real.log T) / eta)) / 2 ≤
        -32 * Real.log (Real.log T) := by
    nlinarith
  have hthird : -pintzMobiusLambdaThreshold / 2 ≤ 0 := by
    nlinarith
  calc
    16 * fordSourceB 3000000 * eta *
          (Real.sqrt eta * Real.log T) -
        (256 * (1 + fordSourceB 3000000) * Real.sqrt eta * Real.log T +
            64 * Real.log (Real.log T) / eta +
            pintzMobiusLambdaThreshold) / 2 =
      (16 * fordSourceB 3000000 * eta *
            (Real.sqrt eta * Real.log T) -
          (256 * (1 + fordSourceB 3000000) *
            (Real.sqrt eta * Real.log T)) / 2) +
        (-(64 * (Real.log (Real.log T) / eta)) / 2) +
        (-pintzMobiusLambdaThreshold / 2) := by ring
    _ ≤ 0 + (-32 * Real.log (Real.log T)) + 0 := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = -32 * Real.log (Real.log T) := by ring

theorem pintz_error_exp_decay
    {eta T : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.exp (-pintzDensityLambda eta T / 2) ≤
      Real.log T ^ (-32 : ℝ) := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogPos : 0 < Real.log T := by
    have hDpos := vinogradovKorobovDenominator_pos hT
    have hDle := vinogradovKorobovDenominator_le_log hT
    linarith
  rw [Real.rpow_def_of_pos hTpos, Real.rpow_def_of_pos hlogPos,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := pintz_error_exponent_le heta hetaUpper hT
  linarith

theorem pintz_error_bare_exp_decay
    {eta T : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    Real.exp (-pintzDensityLambda eta T / 2) ≤
      Real.log T ^ (-32 : ℝ) := by
  have hTOne : (1 : ℝ) ≤ T := by
    have hExp : (1 : ℝ) ≤ Real.exp (Real.exp 1) :=
      (Real.one_le_exp (Real.exp_pos 1).le)
    exact hExp.trans hT
  have hpowOne : 1 ≤
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) := by
    exact Real.one_le_rpow hTOne (mul_nonneg pintzZetaExponentCoefficient_pos.le
      (Real.rpow_nonneg heta.le _))
  calc
    Real.exp (-pintzDensityLambda eta T / 2) ≤
        T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.exp (-pintzDensityLambda eta T / 2) := by
      exact (le_mul_iff_one_le_left (Real.exp_pos _)).mpr hpowOne
    _ ≤ Real.log T ^ (-32 : ℝ) :=
      pintz_error_exp_decay heta hetaUpper hT

noncomputable def pintzContourFinalCoefficient (c : ℝ) : ℝ :=
  pintzContourErrorCoefficient * (1 + pintzZetaEnvelopeCoefficient) *
    (pintzDensityLambdaLogCoefficient c + 5)

theorem pintzContourFinalCoefficient_pos
    {c : ℝ} (hc : 0 < c) : 0 < pintzContourFinalCoefficient c := by
  unfold pintzContourFinalCoefficient
  have hE := pintzContourErrorCoefficient_pos
  have hZ := pintzZetaEnvelopeCoefficient_pos
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  positivity

theorem pintz_uniform_contour_error_le_log_decay
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzUniformEquation46ErrorBound (pintzDensityLambda eta T)
        (pintzPhysicalZetaMajorant eta T) ≤
      pintzContourFinalCoefficient c * Real.log T ^ (-29 : ℝ) := by
  have hTExp : Real.exp 1 ≤ T := by
    exact (Real.exp_le_exp.mpr
      (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
  have hlogOne : 1 ≤ Real.log T := by
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTExp
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hTpos hTExp
  have hlogNonneg : 0 ≤ Real.log T := zero_le_one.trans hlogOne
  have hlambdaEight : 8 ≤ pintzDensityLambda eta T :=
    pintzMobiusLambdaThreshold_ge_eight.trans
      (pintzDensityLambda_ge_threshold heta.le hTExp)
  have hZnonneg : 0 ≤ pintzPhysicalZetaMajorant eta T := by
    unfold pintzPhysicalZetaMajorant
    have := pintzHorizontalZetaMajorant_nonneg (eta := eta)
      (T := T) (by
        have hTOne : (1 : ℝ) ≤ T :=
          (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hTExp
        linarith)
    linarith
  have hraw := pintzUniformEquation46ErrorBound_le_errorEnvelope
    hlambdaEight hZnonneg
  have hZ := pintzPhysicalZetaMajorant_le_power_log heta.le hT
  have hlambda := pintzDensityLambda_le_log_sq hc heta (by linarith) hT hetaAbove
  have hbare := pintz_error_bare_exp_decay heta hetaUpper hT
  have hweighted := pintz_error_exp_decay heta hetaUpper hT
  have hpowNonneg : 0 ≤ Real.log T ^ (-32 : ℝ) :=
    Real.rpow_nonneg hlogNonneg _
  have hpowerTNonneg : 0 ≤
      T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) := by
    have hTnonneg : 0 ≤ T := by
      have hTOne : (1 : ℝ) ≤ T :=
        (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hTExp
      linarith
    exact Real.rpow_nonneg hTnonneg _
  have hZlogNonneg : 0 ≤ pintzZetaEnvelopeCoefficient * Real.log T :=
    mul_nonneg pintzZetaEnvelopeCoefficient_pos.le hlogNonneg
  have hOnePlus :
      (1 + pintzPhysicalZetaMajorant eta T) *
          Real.exp (-pintzDensityLambda eta T / 2) ≤
        (1 + pintzZetaEnvelopeCoefficient * Real.log T) *
          Real.log T ^ (-32 : ℝ) := by
    calc
      _ = Real.exp (-pintzDensityLambda eta T / 2) +
          pintzPhysicalZetaMajorant eta T *
            Real.exp (-pintzDensityLambda eta T / 2) := by ring
      _ ≤ Real.log T ^ (-32 : ℝ) +
          (pintzZetaEnvelopeCoefficient * Real.log T) *
            Real.log T ^ (-32 : ℝ) := by
        apply add_le_add hbare
        calc
          pintzPhysicalZetaMajorant eta T *
              Real.exp (-pintzDensityLambda eta T / 2) ≤
            (pintzZetaEnvelopeCoefficient *
                T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
                Real.log T) *
              Real.exp (-pintzDensityLambda eta T / 2) := by
            gcongr
          _ = (pintzZetaEnvelopeCoefficient * Real.log T) *
              (T ^ (pintzZetaExponentCoefficient * eta ^ (3 / 2 : ℝ)) *
                Real.exp (-pintzDensityLambda eta T / 2)) := by ring
          _ ≤ (pintzZetaEnvelopeCoefficient * Real.log T) *
              Real.log T ^ (-32 : ℝ) := by
            gcongr
      _ = _ := by ring
  have hlambdaFive : pintzDensityLambda eta T + 5 ≤
      (pintzDensityLambdaLogCoefficient c + 5) * Real.log T ^ 2 := by
    have hsqOne : 1 ≤ Real.log T ^ 2 := by nlinarith
    have hfiveRaw := mul_le_mul_of_nonneg_left hsqOne
      (show (0 : ℝ) ≤ 5 by norm_num)
    have hfive : (5 : ℝ) ≤ 5 * Real.log T ^ 2 := by
      simpa using hfiveRaw
    calc
      pintzDensityLambda eta T + 5 ≤
          pintzDensityLambdaLogCoefficient c * Real.log T ^ 2 +
            5 * Real.log T ^ 2 := add_le_add hlambda hfive
      _ = _ := by ring
  have hlogFactor : 1 + pintzZetaEnvelopeCoefficient * Real.log T ≤
      (1 + pintzZetaEnvelopeCoefficient) * Real.log T := by
    nlinarith [pintzZetaEnvelopeCoefficient_pos.le]
  have hContourNonneg : 0 ≤ pintzContourErrorCoefficient :=
    pintzContourErrorCoefficient_pos.le
  have hLambdaFactorNonneg : 0 ≤
      (pintzDensityLambdaLogCoefficient c + 5) * Real.log T ^ 2 := by
    exact mul_nonneg (by linarith [pintzDensityLambdaLogCoefficient_pos hc])
      (sq_nonneg _)
  have hFirstFactorNonneg : 0 ≤
      (1 + pintzZetaEnvelopeCoefficient * Real.log T) *
        Real.log T ^ (-32 : ℝ) := by
    exact mul_nonneg (by linarith) hpowNonneg
  calc
    pintzUniformEquation46ErrorBound (pintzDensityLambda eta T)
        (pintzPhysicalZetaMajorant eta T) ≤
      pintzContourErrorCoefficient *
        (1 + pintzPhysicalZetaMajorant eta T) *
        (pintzDensityLambda eta T + 5) *
        Real.exp (-pintzDensityLambda eta T / 2) := hraw
    _ = pintzContourErrorCoefficient *
        ((1 + pintzPhysicalZetaMajorant eta T) *
          Real.exp (-pintzDensityLambda eta T / 2)) *
        (pintzDensityLambda eta T + 5) := by ring
    _ ≤ pintzContourErrorCoefficient *
        ((1 + pintzZetaEnvelopeCoefficient * Real.log T) *
          Real.log T ^ (-32 : ℝ)) *
        ((pintzDensityLambdaLogCoefficient c + 5) * Real.log T ^ 2) := by
      gcongr
    _ ≤ pintzContourErrorCoefficient *
        (((1 + pintzZetaEnvelopeCoefficient) * Real.log T) *
          Real.log T ^ (-32 : ℝ)) *
        ((pintzDensityLambdaLogCoefficient c + 5) * Real.log T ^ 2) := by
      gcongr
    _ = pintzContourFinalCoefficient c * Real.log T ^ (-29 : ℝ) := by
      unfold pintzContourFinalCoefficient
      have hcombine : Real.log T * Real.log T ^ (-32 : ℝ) *
          Real.log T ^ (2 : ℕ) = Real.log T ^ (-29 : ℝ) := by
        have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlogOne
        calc
          Real.log T * Real.log T ^ (-32 : ℝ) * Real.log T ^ (2 : ℕ) =
              (Real.log T ^ (1 : ℝ) * Real.log T ^ (-32 : ℝ)) *
                Real.log T ^ (2 : ℕ) := by rw [Real.rpow_one]
          _ = Real.log T ^ ((1 : ℝ) + (-32 : ℝ)) *
                Real.log T ^ (2 : ℕ) := by rw [← Real.rpow_add hlogPos]
          _ = Real.log T ^ ((1 : ℝ) + (-32 : ℝ)) *
                Real.log T ^ (2 : ℝ) := by
            congr 1
            exact (Real.rpow_natCast (Real.log T) 2).symm
          _ = Real.log T ^ (((1 : ℝ) + (-32 : ℝ)) + 2) := by
            rw [← Real.rpow_add hlogPos]
          _ = Real.log T ^ (-29 : ℝ) := by norm_num
      calc
        _ = pintzContourErrorCoefficient *
            (1 + pintzZetaEnvelopeCoefficient) *
            (pintzDensityLambdaLogCoefficient c + 5) *
            (Real.log T * Real.log T ^ (-32 : ℝ) *
              Real.log T ^ (2 : ℕ)) := by ring
        _ = _ := by rw [hcombine]

noncomputable def pintzContourErrorHeight (c : ℝ) : ℝ :=
  Real.exp (max (Real.exp 1) (4 * pintzContourFinalCoefficient c))

theorem pintz_uniform_contour_error_le_quarter
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : pintzContourErrorHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    pintzUniformEquation46ErrorBound (pintzDensityLambda eta T)
        (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4 := by
  have hbase : Real.exp (Real.exp 1) ≤ pintzContourErrorHeight c := by
    unfold pintzContourErrorHeight
    exact Real.exp_le_exp.mpr (le_max_left _ _)
  have hlarge := pintz_uniform_contour_error_le_log_decay hc heta hetaUpper
    (hbase.trans hT) hetaAbove
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogCoeff : 4 * pintzContourFinalCoefficient c ≤ Real.log T := by
    have hexp : Real.exp (4 * pintzContourFinalCoefficient c) ≤ T :=
      (Real.exp_le_exp.mpr (le_max_right _ _)).trans hT
    simpa only [Real.le_log_iff_exp_le hTpos] using hexp
  have hlogOne : 1 ≤ Real.log T := by
    have honeExp : (1 : ℝ) ≤ Real.exp 1 :=
      (Real.one_lt_exp_iff.mpr zero_lt_one).le
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr (honeExp.trans (le_max_left _ _))).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hneg : Real.log T ^ (-29 : ℝ) ≤ (Real.log T)⁻¹ := by
    simpa [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num : (-29 : ℝ) ≤ -1)
  have hCpos := pintzContourFinalCoefficient_pos hc
  calc
    _ ≤ pintzContourFinalCoefficient c * Real.log T ^ (-29 : ℝ) := hlarge
    _ ≤ pintzContourFinalCoefficient c * (Real.log T)⁻¹ :=
      mul_le_mul_of_nonneg_left hneg hCpos.le
    _ ≤ 1 / 4 := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ (by linarith : 0 < Real.log T)).2 (by linarith)

#print axioms pintz_error_exponent_le
#print axioms pintz_uniform_contour_error_le_quarter

end

end GafniTao
