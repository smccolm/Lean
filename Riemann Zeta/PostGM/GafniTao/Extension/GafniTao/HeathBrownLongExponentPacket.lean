import GafniTao.HeathBrownLongCommonThresholds
import GafniTao.HeathBrownActualExponentPacket

/-!
# Finite exponent packet for every long detector colour

This is the branch-independent counterpart of the earlier Type-II-only
packet.  It consumes the actual long-colour output, selects the real common
powered-energy witness stored there, and exposes the two cardinality bounds
and the self-energy relation at their exact logarithmic bases.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The complete source exponent packet for either actual detector label,
provided its selected physical length lies beyond the square threshold. -/
theorem eventually_heathBrownLong_exponentPacket
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
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
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
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
        let sigma0 := heathBrownLongEffectiveSigma sigma delta2 eta
          zetaShell zetaConst (P + 1) - zetaDil
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
  obtain ⟨Ux, _hUx, hXfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta2 / 4) (b := delta2 / 2) (by positivity) (by linarith)
  obtain ⟨Uy, _hUy, hYfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta1 / 2) (b := delta1) (by positivity) (by linarith)
  have hXgrow : ∀ᶠ U : Real in atTop, (2 : Real) <= U ^ (delta2 / 4) :=
    (tendsto_rpow_atTop (show 0 < delta2 / 4 by positivity)).eventually
      (eventually_ge_atTop 2)
  have hThreshold := eventually_heathBrownLong_commonThresholds
    (sigma := sigma) (delta := delta) (epsilon := epsilon)
    (Cmv := Cmv) (C0 := C0) (C2 := C2) (C4 := C4)
    hdelta1 hdelta2 hsigmaUpper heta hzetaShell hzetaConst hzetaDil hC hCp
  have hLoss := eventually_heathBrown_finite_loss_le_power
    (P := P) (C2 := C2) (C4 := C4) hzetaRel hRelMargin hC0.le
  have hCardCoeff := eventually_heathBrown_cardinality_coefficients
    (P := P) hCmv hzetaCard
  filter_upwards [eventually_ge_atTop Ux, eventually_ge_atTop Uy, hXgrow,
      hThreshold, hLoss, hCardCoeff, eventually_ge_atTop (1 : Real)]
    with U hUxU hUyU hXgrowU hThresholdU hLossU hCardCoeffU hU
  intro d label out hW
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma eta C label.1
  let full := Classical.choice out.outputs
  have hThresholdData := hThresholdU d label out
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
  let sigma0 := heathBrownLongEffectiveSigma sigma delta2 eta
    zetaShell zetaConst (P + 1) - zetaDil
  have hNOne : 1 < N := by
    have hSelectedLower :
        Nat.floor (U ^ (delta2 / 2)) <= N := by
      cases hlabel : binaryScaleLabel label.1 with
      | inl r =>
          have hY := le_classicalBinarySelectedN_of_typeI
            (Y := Nat.floor (U ^ delta1))
            (X := Nat.floor (U ^ (delta2 / 2))) label.1 r hlabel
          exact (by
            have hXY : Nat.floor (U ^ (delta2 / 2)) <=
                Nat.floor (U ^ delta1) := by
              exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hU
                (by linarith))
            exact hXY.trans (by simpa only [N] using hY))
      | inr r =>
          simpa only [N] using
            (classicalBinarySelectedN_typeII_range
              (show 0 < Nat.floor (U ^ (delta2 / 2)) by
                have : (0 : Real) < Nat.floor (U ^ (delta2 / 2)) :=
                  zero_lt_one.trans_le ((Real.one_le_rpow hU
                    (by positivity)).trans (hXfloor U hUxU))
                exact_mod_cast this)
              (by rw [d.hkII_eq]) label.1 r hlabel).1
    have hXTwo : 1 < Nat.floor (U ^ (delta2 / 2)) := by
      have hXlower : (2 : Real) <= Nat.floor (U ^ (delta2 / 2)) := by
        calc
          2 <= U ^ (delta2 / 4) := hXgrowU
          _ <= Nat.floor (U ^ (delta2 / 2)) := hXfloor U hUxU
      exact_mod_cast hXlower
    exact hXTwo.trans_le hSelectedLower
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
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx)
      (heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst P -
        zetaDil)).trans_le hThresholdData.1
  have hVNext : 0 < VNext :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext)
      (heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst
        (P + 1) - zetaDil)).trans_le hThresholdData.2
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
  have hSigmaMainP :
      heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst P -
          zetaDil <= sigmaMain := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [sigmaMain, rpow_heathBrownLogExponent hx hV] using
      hThresholdData.1
  have hSigmaMain : sigma0 <= sigmaMain := by
    calc
      sigma0 <=
          heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst P -
            zetaDil := by
        dsimp only [sigma0, heathBrownLongEffectiveSigma]
        push_cast
        have hTotal : 0 <= delta2 + zetaShell :=
          (add_pos hdelta2 hzetaShell).le
        nlinarith
      _ <= sigmaMain := hSigmaMainP
  have hSigmaNext : sigma0 <= sigmaNext := by
    apply (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp
    simpa only [sigma0, sigmaNext, rpow_heathBrownLogExponent hxNext hVNext]
      using hThresholdData.2
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
      calc
        1 <= U ^ (delta2 / 4) := Real.one_le_rpow hU (by positivity)
        _ <= Nat.floor (U ^ (delta2 / 2)) := hXfloor U hUxU
    have hYreal : (1 : Real) <= Nat.floor (U ^ delta1) := by
      calc
        1 <= U ^ (delta1 / 2) := Real.one_le_rpow hU (by positivity)
        _ <= Nat.floor (U ^ delta1) := hYfloor U hUyU
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

#print axioms eventually_heathBrownLong_exponentPacket

end

end GafniTao
