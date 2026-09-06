import GafniTao.HeathBrownTypeILongThresholds
import GafniTao.HeathBrownLongExponentPacket

/-!
# Exponent packet for an actual long Type-I colour

The packet is the literal finite Heath--Brown relation for a retained
Type-I detector label.  Its effective real part comes from the exact-power
threshold theorem, so the physical detector loss is divided by the genuine
lower Type-I scale instead of being multiplied by a uniform power cap.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Complete logarithmic packet attached to an actual nonempty Type-I
colour satisfying the source square condition. -/
theorem eventually_actualTypeI_long_exponentPacket
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4) :
    ∀ᶠ U : Real in atTop,
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kI * 2))
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
        binaryScaleLabel label.1 = Sum.inl r ->
        (classicalBinaryColorFamily d label).Nonempty ->
        let N := classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1
        let p := heathBrownSourcePower N U
        let P := heathBrownLongPowerCap delta2
        let L := classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
        let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
        let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
        let V := heathBrownPoweredThreshold N p L Cp eta
        let VNext := heathBrownPoweredThreshold N (p + 1) L Cp eta
        let E : Real := (ApproxAddEnergy 1
          (classicalBinaryColorFamily d label) : Real)
        let sigmaMain := heathBrownLogExponent x V
        let sigmaNext := heathBrownLogExponent xNext VNext
        let tau := heathBrownLogExponent x ((2 ^ P : Real) * U)
        let rho := heathBrownLogExponent x
          ((classicalBinaryColorFamily d label).card : Real)
        let rhoStar := heathBrownLogExponent x E
        let sigma0 := heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
          zetaShell zetaConst - zetaDil
        sigma0 <= sigmaMain /\ sigma0 <= sigmaNext /\
          1 <= tau /\ tau <= 3 / 2 /\
          rho <= zetaCard + tau + 1 - 2 * sigmaMain /\
          rho <= (3 / 2 : Real) *
            (zetaCard + 2 - 2 * sigmaNext) /\
          rhoStar <= zetaRel +
            (1 - 2 * sigmaMain +
              (1 / 2 : Real) *
                max (rho + 1)
                  (max (2 * rho) (5 * rho / 4 + tau / 2)) +
              (1 / 2 : Real) *
                max (rhoStar + 1)
                  (max (4 * rho)
                    (3 * rhoStar / 4 + rho + tau / 2))) := by
  let P := heathBrownLongPowerCap delta2
  obtain ⟨Uy, _hUy, hYfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta1 / 2) (b := delta1) (by positivity) (by linarith)
  have hYgrow : ∀ᶠ U : Real in atTop, (2 : Real) <= U ^ (delta1 / 2) :=
    (tendsto_rpow_atTop (show 0 < delta1 / 2 by positivity)).eventually
      (eventually_ge_atTop 2)
  have hThreshold := eventually_actualTypeI_long_commonThresholds
    (sigma := sigma) (delta := delta) (epsilon := epsilon)
    (C := C) (Cmv := Cmv) (C0 := C0) (C2 := C2) (C4 := C4)
    hdelta1 hdelta2 hsigmaUpper heta hzetaShell hzetaConst hzetaDil hCp
  have hLoss := eventually_heathBrown_finite_loss_le_power
    (P := P) (C2 := C2) (C4 := C4) hzetaRel hRelMargin hC0.le
  have hCardCoeff := eventually_heathBrown_cardinality_coefficients
    (P := P) hCmv hzetaCard
  filter_upwards [eventually_ge_atTop Uy, hYgrow, hThreshold, hLoss,
      hCardCoeff, eventually_ge_atTop (1 : Real)]
    with U hUyU hYgrowU hThresholdU hLossU hCardCoeffU hU
  intro d label r out hlabel hW
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  let full := Classical.choice out.outputs
  have hThresholdData := hThresholdU d label r out hlabel
  dsimp only at hThresholdData
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let VNext := heathBrownPoweredThreshold N (p + 1) L Cp eta
  let E : Real := (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real)
  let sigmaMain := heathBrownLogExponent x V
  let sigmaNext := heathBrownLogExponent xNext VNext
  let tau := heathBrownLogExponent x ((2 ^ P : Real) * U)
  let rho := heathBrownLogExponent x
    ((classicalBinaryColorFamily d label).card : Real)
  let rhoStar := heathBrownLogExponent x E
  let sigma0 := heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
    zetaShell zetaConst - zetaDil
  have hLowerY : Nat.floor (U ^ delta1) <= N := by
    simpa only [N, classicalBinarySelectedN, hlabel, Sum.elim_inl] using
      (le_classicalBinarySelectedN_of_typeI
        (Y := Nat.floor (U ^ delta1))
        (X := Nat.floor (U ^ (delta2 / 2))) label.1 r hlabel)
  have hNOne : 1 < N := by
    have hFloorTwo : (2 : Real) <= Nat.floor (U ^ delta1) :=
      hYgrowU.trans (hYfloor U hUyU)
    have : 1 < Nat.floor (U ^ delta1) := by exact_mod_cast hFloorTwo
    exact this.trans_le hLowerY
  have hN : 0 < N := by omega
  have hpTwo : 2 <= p := by simpa only [N, p] using out.scale.1
  have hp : 0 < p := by omega
  have hpP : p <= P := by
    have hp0 : p <= Nat.ceil (4 / delta2) := by
      simpa only [N, p] using out.scale.2.2.2.2
    dsimp only [P, heathBrownLongPowerCap]
    omega
  have hBase : ((N ^ p : Nat) : Real) <= U := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.1
  have hNext : U <= ((N ^ (p + 1) : Nat) : Real) := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.2.1.le
  have hCubeMain : U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3 := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.2.2.1
  have hCoeffData := hCardCoeffU N p hN hp hpP hCubeMain
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
        (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hxNext : 1 < xNext := by
    dsimp only [xNext]
    exact_mod_cast (show 1 < 2 ^ P * N ^ (p + 1) by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
        (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hV : 0 < V :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx) sigma0).trans_le
      hThresholdData.1
  have hVNext : 0 < VNext :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext) sigma0).trans_le
      hThresholdData.2
  have hCaps := full.common_cardinality_exponents
    (sigmaMain := sigmaMain) (sigmaNext := sigmaNext)
    hNOne hpTwo hpP (zero_lt_one.trans_le hU) hCmv hW rfl hBase hNext
    hCubeMain
    (le_of_eq (by simpa only [sigmaMain, x, V] using
      rpow_heathBrownLogExponent hx hV))
    (le_of_eq (by simpa only [sigmaNext, xNext, VNext] using
      rpow_heathBrownLogExponent hxNext hVNext))
    hCoeffData.1 hCoeffData.2
  dsimp only at hCaps
  have hSigmaMain : sigma0 <= sigmaMain := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [sigmaMain, rpow_heathBrownLogExponent hx hV] using
      hThresholdData.1
  have hSigmaNext : sigma0 <= sigmaNext := by
    apply (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp
    simpa only [sigmaNext, rpow_heathBrownLogExponent hxNext hVNext] using
      hThresholdData.2
  have hLossSmall := hLossU N p hN hp hpP hCubeMain
  have hSmallBase : ((2 ^ p * N ^ p : Nat) : Real) <= x := by
    dsimp only [x]
    exact_mod_cast Nat.mul_le_mul_right (N ^ p)
      (Nat.pow_le_pow_right (by omega) hpP)
  have hLossCommon :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          (((2 ^ P : Real) * U) ^ epsilon) <= x ^ zetaRel :=
    hLossSmall.trans (Real.rpow_le_rpow (by positivity) hSmallBase hzetaRel.le)
  have hL : 0 < L := by
    have hXreal : (1 : Real) <= Nat.floor (U ^ (delta2 / 2)) := by
      have hExp : 0 <= delta2 / 2 := by positivity
      have hXnat : 0 < Nat.floor (U ^ (delta2 / 2)) :=
        Nat.floor_pos.mpr (Real.one_le_rpow hU hExp)
      exact_mod_cast hXnat
    have hYreal : (1 : Real) <= Nat.floor (U ^ delta1) := by
      exact (show (1 : Real) <= Nat.floor (U ^ delta1) by
        linarith [hYgrowU, hYfloor U hUyU])
    exact classicalBinarySelectedThreshold_pos
      (by exact_mod_cast hYreal) (by exact_mod_cast hXreal)
      (by have := d.hkI; omega) (by have := d.hkII; omega)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) hC label.1
  have hRelation := full.logarithmic_relation_common hN hp hpP hL
    (by positivity) hC0.le hC2.le hC4.le hW
    (by simpa only [x] using hLossCommon)
  dsimp only at hRelation
  simpa only [N, p, P, L, x, xNext, V, VNext, E, sigmaMain,
    sigmaNext, tau, rho, rhoStar, sigma0] using
    ⟨hSigmaMain, hSigmaNext, hCaps.1, hCaps.2.1, hCaps.2.2.2.1,
      hCaps.2.2.2.2, hRelation⟩

#print axioms eventually_actualTypeI_long_exponentPacket

end

end GafniTao
