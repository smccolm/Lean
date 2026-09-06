import GafniTao.HeathBrownActualCardinalityExponents
import GafniTao.HeathBrownCommonLogarithmicRelation
import GafniTao.HeathBrownLossyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# A source-independent physical Heath--Brown cell consumer

This module isolates the part of the low-cell argument that depends only on
an actual fully uniform powered output, its two consecutive thresholds, and
the exact power-choice window.  It is used for the reflected Type-I blocks,
whose source threshold is different from the original Type-II detector.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Any actual fully uniform source output satisfying the common-base
thresholds obeys the low Heath--Brown physical energy estimate. -/
theorem eventually_generic_powered_physical_low_cells
    {P : Nat}
    {epsilon zetaRel zetaCard Cmv C0 C2 C4 sigma0 : Real}
    (hCmv : 0 < Cmv) (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hzetaRel : 0 < zetaRel) (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hsigma0Lower : 1 / 2 ≤ sigma0)
    (hsigma0Upper : sigma0 ≤ 3 / 4) :
    ∀ᶠ U : Real in atTop,
      ∀ {R eta L sigmaMain sigmaNext Cp : Real} {N p : Nat}
          (W : Finset Real) (a : Nat → Complex)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ P : Real) * U) R N p eta L W a
            Cp Cmv C0 C2 C4),
        1 ≤ U → 1 < N → 2 ≤ p → p ≤ P → 0 < L →
        W.Nonempty →
        ((N ^ p : Nat) : Real) ≤ U →
        U ≤ ((N ^ (p + 1) : Nat) : Real) →
        U ^ 2 ≤ ((N ^ p : Nat) : Real) ^ 3 →
        (((2 ^ P * N ^ p : Nat) : Real) ^ sigmaMain ≤
          heathBrownPoweredThreshold N p L Cp eta) →
        (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ sigmaNext ≤
          heathBrownPoweredThreshold N (p + 1) L Cp eta) →
        sigma0 ≤ sigmaMain → sigma0 ≤ sigmaNext →
        (ApproxAddEnergy 1 W : Real) ≤
          ((2 ^ P : Real) * U) ^
            (max (heathBrownLowFirstSlope sigma0)
                (heathBrownLowSecondSlope sigma0) +
              4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  have hLoss := eventually_heathBrown_finite_loss_le_power
    (P := P) (C2 := C2) (C4 := C4) hzetaRel hRelMargin hC0.le
  have hCardCoeff := eventually_heathBrown_cardinality_coefficients
    (P := P) hCmv hzetaCard
  filter_upwards [hLoss, hCardCoeff] with U hLossU hCardCoeffU
  intro R eta L sigmaMain sigmaNext Cp N p W a _full hU hN hp hpP hL hW
    hBase hNext hCube hThreshold hThresholdNext hSigmaMain hSigmaNext
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
  have hNpos : 0 < N := by omega
  have hppos : 0 < p := by omega
  have hUpos : 0 < U := zero_lt_one.trans_le hU
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
  have hFiniteLoss := hLossU N p hNpos hppos hpP hCube
  have hFiniteLossCommon :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          (((2 ^ P : Real) * U) ^ epsilon) ≤
        (((2 ^ P * N ^ p : Nat) : Real) ^ zetaRel) := by
    apply hFiniteLoss.trans
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast Nat.mul_le_mul_right (N ^ p)
        (Nat.pow_le_pow_right (by omega : 0 < 2) hpP)
    · exact hzetaRel.le
  have hCoefficients := hCardCoeffU N p hNpos hppos hpP hCube
  have hThresholdLog :
      (((2 ^ P * N ^ p : Nat) : Real) ^ sigmaLog ≤
        heathBrownPoweredThreshold N p L Cp eta) := by
    calc
      ((2 ^ P * N ^ p : Nat) : Real) ^ sigmaLog = V := by
        simpa only [sigmaLog, x] using
          (rpow_heathBrownLogExponent hx hV)
      _ ≤ heathBrownPoweredThreshold N p L Cp eta := le_rfl
  have hThresholdNextLog :
      (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ sigmaLogNext ≤
        heathBrownPoweredThreshold N (p + 1) L Cp eta) := by
    calc
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ sigmaLogNext = VNext := by
        simpa only [sigmaLogNext, xNext] using
          (rpow_heathBrownLogExponent hxNext hVNext)
      _ ≤ heathBrownPoweredThreshold N (p + 1) L Cp eta := le_rfl
  have hCard := _full.common_cardinality_exponents hN hp hpP hUpos hCmv hW
    rfl hBase hNext hCube hThresholdLog hThresholdNextLog
      hCoefficients.1 hCoefficients.2
  dsimp only at hCard
  have hRelation := _full.logarithmic_relation_common hNpos hppos hpP hL
    hBpos hC0.le hC2.le hC4.le hW hFiniteLossCommon
  dsimp only [B, x, xNext, V, VNext, E, sigmaLog, sigmaLogNext,
    tau, rho, rhoStar] at hRelation ⊢
  have hCell := heathBrown_lossy_low_cells hsigma0Lower hsigma0Upper
    (hSigmaMain.trans hSigmaToLog) (hSigmaNext.trans hSigmaNextToLog)
    hCard.1 hCard.2.1 hzetaRel.le hzetaCard.le
    hCard.2.2.2.1 hCard.2.2.2.2 hRelation
  have hEnergy : 0 < (ApproxAddEnergy 1 W : Real) := by
    have hCardPos : 0 < W.card := Finset.card_pos.mpr hW
    have hEnergyNat : W.card ^ 2 ≤ ApproxAddEnergy 1 W :=
      card_sq_le_approxAddEnergy (by norm_num) W
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCardPos 2) hEnergyNat)
  have hxB : ((2 ^ P * N ^ p : Nat) : Real) ≤
      (2 ^ P : Real) * U := by
    calc
      ((2 ^ P * N ^ p : Nat) : Real) =
          (2 ^ P : Real) * ((N ^ p : Nat) : Real) := by norm_num
      _ ≤ (2 ^ P : Real) * U :=
        mul_le_mul_of_nonneg_left hBase (by positivity)
  exact heathBrown_physical_of_packet_bound hx hEnergy
    (by positivity) hxB
    (by unfold heathBrownCardinalityShift; positivity) rfl rfl hCell

#print axioms eventually_generic_powered_physical_low_cells

end

end GafniTao
