import GafniTao.PintzSelectionEnvelope

/-!
# A single explicit envelope for the native Pintz count

The finite zero count has two terms.  The low-height term costs three powers
of `log T`.  The detected term costs `263 + 260 = 523` powers and doubles the
power-bearing exponent from `4 L eta^(3/2)` to `8 L eta^(3/2)`.
-/

namespace GafniTao

noncomputable section

noncomputable def pintzCentralEnvelopeCoefficient (c : ℝ) : ℝ :=
  2 * (4 * pintzDensityLambdaLogCoefficient c + 9) *
    (globalLocalZeroLogConstant + 1)

noncomputable def pintzDiagonalEnvelopeCoefficient (c : ℝ) : ℝ :=
  pintzHarmonicEnvelopeCoefficient c ^ 2 *
    pintzCutoffPowerCoefficient / 2

noncomputable def pintzNativeEnvelopeCoefficient (c : ℝ) : ℝ :=
  pintzCentralEnvelopeCoefficient c +
    pintzSelectionEnvelopeCoefficient c *
      pintzDiagonalEnvelopeCoefficient c

theorem pintzCentralEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzCentralEnvelopeCoefficient c := by
  unfold pintzCentralEnvelopeCoefficient
  have hL := pintzDensityLambdaLogCoefficient_pos hc
  have hZ := globalLocalZeroLogConstant_pos
  positivity

theorem pintzDiagonalEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzDiagonalEnvelopeCoefficient c := by
  unfold pintzDiagonalEnvelopeCoefficient
  exact div_pos
    (mul_pos (sq_pos_of_pos (pintzHarmonicEnvelopeCoefficient_pos hc))
      pintzCutoffPowerCoefficient_pos) (by norm_num)

theorem pintzNativeEnvelopeCoefficient_pos
    {c : ℝ} (hc : 0 < c) :
    0 < pintzNativeEnvelopeCoefficient c := by
  unfold pintzNativeEnvelopeCoefficient
  exact add_pos_of_pos_of_nonneg (pintzCentralEnvelopeCoefficient_pos hc)
    (mul_nonneg (pintzSelectionEnvelopeCoefficient_pos hc).le
      (pintzDiagonalEnvelopeCoefficient_pos hc).le)

theorem pintz_central_term_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
      Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) ≤
      pintzCentralEnvelopeCoefficient c * Real.log T ^ 3 := by
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hT
  have hlogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hT hetaAbove
  have hlambdaPos : 0 < pintzDensityLambda eta T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hT
    exact pintzDensityLambda_pos heta.le hExp
  have hceilH :
      (Nat.ceil (2 * pintzDensityLambda eta T + 3) : ℝ) ≤
        2 * pintzDensityLambda eta T + 4 := by
    have hceil := (Nat.ceil_lt_add_one (by positivity :
      0 ≤ 2 * pintzDensityLambda eta T + 3)).le
    linarith
  have hfactorH :
      2 * (Nat.ceil (2 * pintzDensityLambda eta T + 3) : ℝ) + 1 ≤
        (4 * pintzDensityLambdaLogCoefficient c + 9) *
          Real.log T ^ 2 := by
    have hsqOne : 1 ≤ Real.log T ^ 2 := by nlinarith
    nlinarith [mul_nonneg
      (pintzDensityLambdaLogCoefficient_pos hc).le
      (sq_nonneg (Real.log T))]
  have hlocalArg : 0 ≤ globalLocalZeroLogConstant * Real.log T :=
    mul_nonneg globalLocalZeroLogConstant_pos.le (zero_le_one.trans hlogOne)
  have hceilLocal :
      (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
        globalLocalZeroLogConstant * Real.log T + 1 :=
    (Nat.ceil_lt_add_one hlocalArg).le
  have hfactorLocal :
      (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ) ≤
        (globalLocalZeroLogConstant + 1) * Real.log T := by
    nlinarith
  unfold pintzCentralEnvelopeCoefficient
  have hfactorHNonneg : 0 ≤
      (4 * pintzDensityLambdaLogCoefficient c + 9) * Real.log T ^ 2 :=
    mul_nonneg (by linarith [pintzDensityLambdaLogCoefficient_pos hc])
      (sq_nonneg _)
  calc
    2 * ((2 * (Nat.ceil (2 * pintzDensityLambda eta T + 3) : ℝ) + 1) *
        (Nat.ceil (globalLocalZeroLogConstant * Real.log T) : ℝ)) ≤
      2 * (((4 * pintzDensityLambdaLogCoefficient c + 9) *
          Real.log T ^ 2) *
        ((globalLocalZeroLogConstant + 1) * Real.log T)) := by
      gcongr
    _ = 2 * (4 * pintzDensityLambdaLogCoefficient c + 9) *
        (globalLocalZeroLogConstant + 1) * Real.log T ^ 3 := by ring

theorem pintz_diagonal_term_le_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : Real.exp (Real.exp 1) ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (harmonic (pintzMobiusCutoff
        (pintzDensityLambda eta T)) : ℝ) ^ 2 *
        (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
          (4 * eta) / 2 ≤
      pintzDiagonalEnvelopeCoefficient c *
        T ^ (4 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
  have hH := pintz_harmonic_le_envelope
    hc heta (by linarith) hT hetaAbove
  have hcutoff := pintz_cutoff_rpow_four_eta_le heta hetaUpper hT
  have hHnonneg : 0 ≤
      (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hHupperNonneg : 0 ≤
      pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2 :=
    mul_nonneg (pintzHarmonicEnvelopeCoefficient_pos hc).le (sq_nonneg _)
  have hHsq :
      (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) ^ 2 ≤
        (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2) ^ 2 := by
    nlinarith [sq_nonneg
      (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2 -
        (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ))]
  have hlogCombine :
      Real.log T ^ (4 : ℕ) *
          Real.log T ^ (4 * pintzDensityLogReserve) =
        Real.log T ^ (260 : ℝ) := by
    rw [show Real.log T ^ (4 * pintzDensityLogReserve) =
        Real.log T ^ (256 : ℕ) by
      unfold pintzDensityLogReserve
      norm_num
      ]
    rw [show Real.log T ^ (260 : ℝ) = Real.log T ^ (260 : ℕ) by
      exact Real.rpow_natCast _ 260]
    ring
  unfold pintzDiagonalEnvelopeCoefficient
  calc
    (harmonic (pintzMobiusCutoff
        (pintzDensityLambda eta T)) : ℝ) ^ 2 *
        (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
          (4 * eta) / 2 ≤
      (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2) ^ 2 *
        (pintzCutoffPowerCoefficient *
          T ^ (4 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (4 * pintzDensityLogReserve)) / 2 := by gcongr
    _ = pintzHarmonicEnvelopeCoefficient c ^ 2 *
        pintzCutoffPowerCoefficient / 2 *
        T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (260 : ℝ) := by
      rw [show
        (pintzHarmonicEnvelopeCoefficient c * Real.log T ^ 2) ^ 2 *
            (pintzCutoffPowerCoefficient *
              T ^ (4 * pintzDensityLambdaCoefficient *
                eta ^ (3 / 2 : ℝ)) *
              Real.log T ^ (4 * pintzDensityLogReserve)) / 2 =
          pintzHarmonicEnvelopeCoefficient c ^ 2 *
            pintzCutoffPowerCoefficient / 2 *
            T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
            (Real.log T ^ (4 : ℕ) *
              Real.log T ^ (4 * pintzDensityLogReserve)) by ring]
      rw [hlogCombine]

theorem pintz_zeroCount_native_envelope
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hBasic : max (Real.exp 2) 8 ≤ T)
    (hErrorHeight : pintzContourErrorHeight c ≤ T)
    (hCoreHeight : pintzCoreAbsorptionHeight c ≤ T)
    (hLambdaHeight : 2 * pintzDensityLambda eta T ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (zeroCount (1 - eta) T : ℝ) ≤
      pintzNativeEnvelopeCoefficient c *
        T ^ (8 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (523 : ℝ) := by
  have hBase : Real.exp (Real.exp 1) ≤ T := by
    unfold pintzContourErrorHeight at hErrorHeight
    exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hErrorHeight
  have hcount := pintz_zeroCount_native_bound hc heta hetaUpper hBasic
    hErrorHeight hCoreHeight hLambdaHeight hetaAbove
  have hcentral := pintz_central_term_le_envelope
    hc heta (by linarith) hBase hetaAbove
  have hselection := pintz_selectionLoss_le_envelope
    hc heta hetaUpper hBase hCoreHeight hetaAbove
  have hdiagonal := pintz_diagonal_term_le_envelope
    hc heta hetaUpper hBase hetaAbove
  have hTpos : 0 < T := (Real.exp_pos _).trans_le hBase
  have hlogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hBase
    exact (Real.le_log_iff_exp_le hTpos).2 hExp
  have hTone : 1 ≤ T := by
    have hone : 1 ≤ Real.exp (Real.exp 1) :=
      Real.one_le_exp (Real.exp_pos 1).le
    exact hone.trans hBase
  have hpowerOne : 1 ≤ T ^ (8 * pintzDensityLambdaCoefficient *
      eta ^ (3 / 2 : ℝ)) := by
    apply Real.one_le_rpow hTone
    exact mul_nonneg
      (mul_nonneg (by norm_num) pintzDensityLambdaCoefficient_pos.le)
      (Real.rpow_nonneg heta.le _)
  have hlog523One : 1 ≤ Real.log T ^ (523 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hcentralFull :
      2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) ≤
        pintzCentralEnvelopeCoefficient c *
          T ^ (8 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) * Real.log T ^ (523 : ℝ) := by
    calc
      _ ≤ pintzCentralEnvelopeCoefficient c * Real.log T ^ 3 := hcentral
      _ ≤ pintzCentralEnvelopeCoefficient c *
          T ^ (8 * pintzDensityLambdaCoefficient *
            eta ^ (3 / 2 : ℝ)) * Real.log T ^ (523 : ℝ) := by
        have hlog3 : 0 ≤ Real.log T ^ 3 := by positivity
        have hlog3le : Real.log T ^ 3 ≤ Real.log T ^ (523 : ℝ) := by
          rw [show Real.log T ^ (523 : ℝ) = Real.log T ^ (523 : ℕ) by
            exact Real.rpow_natCast _ 523]
          exact pow_le_pow_right₀ hlogOne (by omega)
        have hC := (pintzCentralEnvelopeCoefficient_pos hc).le
        have hlog523Nonneg : 0 ≤ Real.log T ^ (523 : ℝ) :=
          Real.rpow_nonneg (zero_le_one.trans hlogOne) _
        have hCP : pintzCentralEnvelopeCoefficient c ≤
            pintzCentralEnvelopeCoefficient c *
              T ^ (8 * pintzDensityLambdaCoefficient *
                eta ^ (3 / 2 : ℝ)) := by
          nlinarith [mul_nonneg hC (sub_nonneg.mpr hpowerOne)]
        calc
          _ ≤ pintzCentralEnvelopeCoefficient c *
              Real.log T ^ (523 : ℝ) :=
            mul_le_mul_of_nonneg_left hlog3le hC
          _ ≤ _ := by
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right hCP hlog523Nonneg
  have hproduct :
      (pintzSelectionLoss (2 * pintzDensityLambda eta T)
          (pintzAdaptiveSeparation c eta T) T : ℝ) *
        ((harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) ^ 2 *
          (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
            (4 * eta) / 2) ≤
      (pintzSelectionEnvelopeCoefficient c *
          pintzDiagonalEnvelopeCoefficient c) *
        T ^ (8 * pintzDensityLambdaCoefficient *
          eta ^ (3 / 2 : ℝ)) * Real.log T ^ (523 : ℝ) := by
    calc
      _ ≤ (pintzSelectionEnvelopeCoefficient c *
            T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) * Real.log T ^ (263 : ℝ)) *
          (pintzDiagonalEnvelopeCoefficient c *
            T ^ (4 * pintzDensityLambdaCoefficient *
              eta ^ (3 / 2 : ℝ)) * Real.log T ^ (260 : ℝ)) := by
        have hselectionUpper : 0 ≤
            pintzSelectionEnvelopeCoefficient c *
              T ^ (4 * pintzDensityLambdaCoefficient *
                eta ^ (3 / 2 : ℝ)) * Real.log T ^ (263 : ℝ) := by
          exact mul_nonneg
            (mul_nonneg (pintzSelectionEnvelopeCoefficient_pos hc).le
              (Real.rpow_nonneg hTpos.le _))
            (Real.rpow_nonneg (zero_le_one.trans hlogOne) _)
        gcongr
      _ = _ := by
        have hpowerCombine :
          T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
              T ^ (4 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) =
            T ^ (8 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) := by
          calc
            _ = T ^ ((4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) +
                (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ))) :=
              (Real.rpow_add hTpos _ _).symm
            _ = _ := by
              congr 1
              ring
        have hlogCombine : Real.log T ^ (263 : ℝ) * Real.log T ^ (260 : ℝ) =
            Real.log T ^ (523 : ℝ) := by
          calc
            _ = Real.log T ^ ((263 : ℝ) + 260) :=
              (Real.rpow_add (zero_lt_one.trans_le hlogOne) _ _).symm
            _ = _ := by norm_num
        calc
          (pintzSelectionEnvelopeCoefficient c *
                T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) * Real.log T ^ (263 : ℝ)) *
              (pintzDiagonalEnvelopeCoefficient c *
                T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) * Real.log T ^ (260 : ℝ)) =
            (pintzSelectionEnvelopeCoefficient c *
              pintzDiagonalEnvelopeCoefficient c) *
              (T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ)) *
                T ^ (4 * pintzDensityLambdaCoefficient *
                  eta ^ (3 / 2 : ℝ))) *
              (Real.log T ^ (263 : ℝ) * Real.log T ^ (260 : ℝ)) := by ring
          _ = _ := by rw [hpowerCombine, hlogCombine]
  unfold pintzNativeEnvelopeCoefficient
  calc
    (zeroCount (1 - eta) T : ℝ) ≤
        2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) +
        (pintzSelectionLoss (2 * pintzDensityLambda eta T)
            (pintzAdaptiveSeparation c eta T) T : ℝ) *
          ((harmonic (pintzMobiusCutoff
              (pintzDensityLambda eta T)) : ℝ) ^ 2 *
            (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
              (4 * eta) / 2) := hcount
    _ ≤ pintzCentralEnvelopeCoefficient c *
          T ^ (8 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (523 : ℝ) +
        (pintzSelectionEnvelopeCoefficient c *
          pintzDiagonalEnvelopeCoefficient c) *
          T ^ (8 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (523 : ℝ) := add_le_add hcentralFull hproduct
    _ = (pintzCentralEnvelopeCoefficient c +
          pintzSelectionEnvelopeCoefficient c *
            pintzDiagonalEnvelopeCoefficient c) *
        T ^ (8 * pintzDensityLambdaCoefficient * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (523 : ℝ) := by ring

#print axioms pintz_zeroCount_native_envelope

end

end GafniTao
