import GafniTao.HeathBrownGenericMHHCardinality
import GafniTao.HeathBrownHighCompanionExponent
import GafniTao.HeathBrownHighFiniteLossAbsorption
import GafniTao.HeathBrownHighLossyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# Source-faithful finite consumer for the high generic energy cell

This is the finite counterpart of lines 155--201 in the pinned ANTEDB proof.
It uses MHH at the main power, the exact mixed MHH/mean-value companion
consumer, and the actual Heath--Brown energy packet.  All fixed losses remain
visible in the concluding exponent.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_generic_powered_physical_high_source_cell
    {P : Nat}
    {epsilon epsilonMHH zetaRel zetaMHH zetaNext
      Cmv Cmhh C0 C2 C4 sigma0 : Real}
    (hCmv : 0 < Cmv) (hCmhh : 0 < Cmhh)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hzetaRel : 0 < zetaRel) (hzetaMHH : 0 < zetaMHH)
    (hzetaNext : 0 < zetaNext) (hepsilonMHH : 0 < epsilonMHH)
    (hRelMargin : epsilon < zetaRel / 2)
    (hsigma0Lower : 3 / 4 ≤ sigma0)
    (hsigma0Upper : sigma0 < 25 / 28)
    (hMHH : ∀ (M : Nat) (B R V : Real) (W : Finset Real)
        (b : Nat → Complex),
      0 < M → 1 ≤ B → (M : Real) ≤ B → 0 < V → 2 * R ≤ B →
      IsSeparated 1 W →
      (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) →
      (W.card : Real) ≤
        Cmhh * B ^ epsilonMHH *
          ((M : Real) ^ 2 / V ^ 2 +
            B * min ((M : Real) / V ^ 2)
              ((M : Real) ^ 4 / V ^ 6))) :
    ∀ᶠ U : Real in atTop,
      ∀ {R eta L sigmaMain sigmaNext Cp : Real} {N p : Nat}
          (W : Finset Real) (a : Nat → Complex)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ P : Real) * U) R N p eta L W a
            Cp Cmv C0 C2 C4),
        1 ≤ U → 1 < N → 2 ≤ p → p + 1 ≤ P → 0 < L → W.Nonempty →
        IsSeparated 1 W → (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
        2 * R ≤ (2 ^ P : Real) * U →
        ((N ^ p : Nat) : Real) ≤ U →
        U ≤ ((N ^ p : Nat) : Real) ^ 2 →
        (((2 ^ P * N ^ p : Nat) : Real) ^ sigmaMain ≤
          heathBrownPoweredThreshold N p L Cp eta) →
        (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ sigmaNext ≤
          heathBrownPoweredThreshold N (p + 1) L Cp eta) →
        sigma0 ≤ sigmaMain → sigma0 ≤ sigmaNext →
        (4 * sigma0 - 1) / 2 ≤
          heathBrownLogExponent ((2 ^ P * N ^ p : Nat) : Real)
            ((2 ^ P : Real) * U) →
        heathBrownLogExponent ((2 ^ P * N ^ p : Nat) : Real)
            ((2 ^ P : Real) * U) ≤ 3 * (4 * sigma0 - 1) / 4 →
        heathBrownLogExponent ((2 ^ P * N ^ (p + 1) : Nat) : Real)
            ((2 ^ P : Real) * U) ≤ 4 * sigma0 - 2 →
        (ApproxAddEnergy 1 W : Real) ≤
          ((2 ^ P : Real) * U) ^
            (heathBrownHighEnergySlope sigma0 +
              4 * (zetaRel + heathBrownHighCardinalityShift
                (heathBrownLogExponent
                  ((2 ^ P * N ^ p : Nat) : Real)
                  ((2 ^ P : Real) * U))
                zetaMHH epsilonMHH (zetaNext + 2 * epsilonMHH))) := by
  have hLoss := eventually_heathBrown_high_finite_loss_le_power
    (P := P) (C2 := C2) (C4 := C4) hzetaRel hRelMargin hC0.le
  have hMainCoeff := eventually_heathBrown_high_cardinality_coefficients
    (P := P) hCmhh hzetaMHH
  have hNextMHHCoeff := eventually_heathBrown_high_cardinality_coefficients
    (P := P) hCmhh hzetaNext
  have hNextMeanCoeff := eventually_heathBrown_high_cardinality_coefficients
    (P := P) hCmv hzetaNext
  filter_upwards [hLoss, hMainCoeff, hNextMHHCoeff, hNextMeanCoeff]
    with U hLossU hMainCoeffU hNextMHHCoeffU hNextMeanCoeffU
  intro R eta L sigmaMain sigmaNext Cp N p W a full hU hN hp hpNextP hL hW
    hSep hSymm hRB hBase hSquare hThreshold hThresholdNext hSigmaMain
    hSigmaNext hTauLower hTauUpper hTauNextShort
  let B : Real := (2 ^ P : Real) * U
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let VNext := heathBrownPoweredThreshold N (p + 1) L Cp eta
  let E : Real := (ApproxAddEnergy 1 W : Real)
  let sigmaLog := heathBrownLogExponent x V
  let sigmaLogNext := heathBrownLogExponent xNext VNext
  let tau := heathBrownLogExponent x B
  let rho := heathBrownLogExponent x (W.card : Real)
  let rhoStar := heathBrownLogExponent x E
  have hpP : p ≤ P := by omega
  have hNpos : 0 < N := by omega
  have hppos : 0 < p := by omega
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      have hNp : 1 < N ^ p := one_lt_pow₀ hN (by omega)
      exact hNp.trans_le (Nat.le_mul_of_pos_left _
        (pow_pos (by norm_num : 0 < (2 : Nat)) P)))
  have hxNext : 1 < xNext := by
    dsimp only [xNext]
    exact_mod_cast (show 1 < 2 ^ P * N ^ (p + 1) by
      have hNp : 1 < N ^ (p + 1) := one_lt_pow₀ hN (by omega)
      exact hNp.trans_le (Nat.le_mul_of_pos_left _
        (pow_pos (by norm_num : 0 < (2 : Nat)) P)))
  have hV : 0 < V :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx) sigmaMain).trans_le
      (by simpa only [x, V] using hThreshold)
  have hVNext : 0 < VNext :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext) sigmaNext).trans_le
      (by simpa only [xNext, VNext] using hThresholdNext)
  have hSigmaToLog : sigmaMain ≤ sigmaLog := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [sigmaLog, rpow_heathBrownLogExponent hx hV, x, V] using
      hThreshold
  have hSigmaNextToLog : sigmaNext ≤ sigmaLogNext := by
    apply (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp
    simpa only [sigmaLogNext, rpow_heathBrownLogExponent hxNext hVNext,
      xNext, VNext] using hThresholdNext
  have hFiniteLoss := hLossU N p hNpos hppos hpP hSquare
  have hFiniteLossCommon :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          (((2 ^ P : Real) * U) ^ epsilon) ≤
        (((2 ^ P * N ^ p : Nat) : Real) ^ zetaRel) := by
    exact hFiniteLoss
  have hMainCoefficients := hMainCoeffU N p hNpos hppos hpNextP hSquare
  have hNextMHH := hNextMHHCoeffU N p hNpos hppos hpNextP hSquare
  have hNextMean := hNextMeanCoeffU N p hNpos hppos hpNextP hSquare
  have hThresholdLog : x ^ sigmaLog ≤ V := by
    exact le_of_eq (rpow_heathBrownLogExponent hx hV)
  have hThresholdNextLog : xNext ^ sigmaLogNext ≤ VNext := by
    exact le_of_eq (rpow_heathBrownLogExponent hxNext hVNext)
  have hRawMHH := full.card.card_le_mhh_common_generic hCmhh.le hMHH hU
    hNpos hppos hpP (by simpa only [Nat.cast_pow] using hBase) hL hRB
    hSep hSymm
  have hCardPos : (0 : Real) < W.card := by
    exact_mod_cast Finset.card_pos.mpr hW
  have hBPower : x ^ tau = B := rpow_heathBrownLogExponent hx hBpos
  have hMHHShift : 2 * ((p : Real) * Cmhh) ≤ x ^ zetaMHH := by
    have hpCoeff : (p : Real) * Cmhh ≤ P * Cmhh := by
      gcongr
    exact (mul_le_mul_of_nonneg_left hpCoeff (by norm_num)).trans
      (by simpa only [x] using hMainCoefficients.1)
  have hMHHLog := heathBrown_mhh_card_log_le hx hBpos hCardPos
    (mul_nonneg (Nat.cast_nonneg p) hCmhh.le) hThresholdLog hBPower
    (by
      simpa only [x, B, V, full.card_Cp, Nat.cast_mul, Nat.cast_pow,
        mul_assoc] using hRawMHH)
    hMHHShift
  have hCompanion := heathBrown_high_companion_exponent_cap full hCmv hCmhh
    hepsilonMHH.le hsigma0Upper (hSigmaNext.trans hSigmaNextToLog) hU hN hp
    hpNextP hL hW hRB hSep hSymm
    (by simpa only [xNext, VNext] using hThresholdNextLog)
    (by simpa only [xNext, B] using hTauNextShort)
    (by simpa only [xNext] using hNextMHH.2)
    (by simpa only [xNext] using hNextMean.2) hMHH
  have hRelation := full.logarithmic_relation_common hNpos hppos hpP hL
    hBpos hC0.le hC2.le hC4.le hW hFiniteLossCommon
  dsimp only [B, x, xNext, V, VNext, E, sigmaLog, sigmaLogNext,
    tau, rho, rhoStar] at hRelation hMHHLog hCompanion
  have hCell := heathBrown_lossy_high_generic_cell hsigma0Lower
    hsigma0Upper (hSigmaMain.trans hSigmaToLog)
    (hSigmaNext.trans hSigmaNextToLog) hTauLower hTauUpper
    hzetaRel.le hzetaMHH.le hepsilonMHH.le
    (by positivity : 0 ≤ zetaNext + 2 * epsilonMHH)
    hMHHLog hCompanion hRelation
  have hEnergy : 0 < (ApproxAddEnergy 1 W : Real) := by
    have hCardNat : 0 < W.card := Finset.card_pos.mpr hW
    have hEnergyNat : W.card ^ 2 ≤ ApproxAddEnergy 1 W :=
      card_sq_le_approxAddEnergy (by norm_num) W
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCardNat 2) hEnergyNat)
  have hxB : ((2 ^ P * N ^ p : Nat) : Real) ≤
      (2 ^ P : Real) * U := by
    calc
      ((2 ^ P * N ^ p : Nat) : Real) =
          (2 ^ P : Real) * ((N ^ p : Nat) : Real) := by norm_num
      _ ≤ (2 ^ P : Real) * U :=
        mul_le_mul_of_nonneg_left hBase (by positivity)
  have hTauNonneg : 0 ≤ heathBrownLogExponent
      ((2 ^ P * N ^ p : Nat) : Real) ((2 ^ P : Real) * U) := by
    have hden : 0 < 4 * sigma0 - 1 := by linarith
    linarith
  have hShift := heathBrownHighCardinalityShift_nonneg hTauNonneg
    hzetaMHH.le hepsilonMHH.le
    (by positivity : 0 ≤ zetaNext + 2 * epsilonMHH)
  exact heathBrown_physical_of_packet_bound hx hEnergy
    (by positivity) hxB (by positivity) rfl rfl hCell

#print axioms eventually_generic_powered_physical_high_source_cell

end
end GafniTao
