import GafniTao.HeathBrownActualCardinalityExponents

/-!
# The actual finite Heath--Brown exponent packet

For a genuine Type-II detector colour, this file assembles the source power
choice, consecutive thresholds, two cardinality packets, and self-energy
moment relation.  Every loss remains an explicit exponent and every
logarithmic variable is defined from the finite object it measures.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The fixed cardinality coefficients of both consecutive packets are
eventually absorbed at their exact common bases. -/
theorem eventually_heathBrown_cardinality_coefficients
    {P : Nat} {Cmv zeta : Real} (hCmv : 0 < Cmv) (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      ∀ (N p : Nat), 0 < N -> 0 < p -> p <= P ->
        U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3 ->
        2 * ((P : Real) * Cmv) <=
            (((2 ^ P * N ^ p : Nat) : Real)) ^ zeta /\
          2 * (((P + 1 : Nat) : Real) * Cmv) <=
            (((2 ^ P * N ^ (p + 1) : Nat) : Real)) ^ zeta := by
  let K : Real := 2 * (((P + 1 : Nat) : Real) * Cmv)
  have hmargin : (0 : Real) < (2 / 3 : Real) * zeta := by positivity
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := K) (a := (0 : Real)) (b := (2 / 3 : Real) * zeta) hmargin
  filter_upwards [hAbsorb, eventually_ge_atTop (1 : Real)]
    with U hAbsorbU hU
  intro N p hN hp hpP hCube
  have hU0 : 0 <= U := zero_le_one.trans hU
  have hLower := rpow_two_thirds_le_of_sq_le_cube hU0
    (Nat.cast_nonneg (N ^ p)) hCube
  have hNpNext : (N ^ p : Nat) <= N ^ (p + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hN
  have hBaseMain : U ^ (2 / 3 : Real) <=
      ((2 ^ P * N ^ p : Nat) : Real) := by
    apply hLower.trans
    exact_mod_cast Nat.le_mul_of_pos_left (N ^ p)
      (pow_pos (by norm_num : (0 : Nat) < 2) P)
  have hBaseNext : U ^ (2 / 3 : Real) <=
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) := by
    apply hBaseMain.trans
    exact_mod_cast Nat.mul_le_mul_left (2 ^ P) hNpNext
  have hK : K <= U ^ ((2 / 3 : Real) * zeta) := by
    simpa only [Real.rpow_zero, mul_one] using hAbsorbU
  have hLift {x : Real} (hx : U ^ (2 / 3 : Real) <= x)
      (hx0 : 0 <= x) : K <= x ^ zeta := by
    calc
      K <= U ^ ((2 / 3 : Real) * zeta) := hK
      _ = (U ^ (2 / 3 : Real)) ^ zeta :=
        Real.rpow_mul hU0 (2 / 3 : Real) zeta
      _ <= x ^ zeta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hU0 _) hx hzeta.le
  have hP : (P : Real) <= (P + 1 : Nat) := by exact_mod_cast Nat.le_add_right P 1
  have hMainK : 2 * ((P : Real) * Cmv) <= K := by
    dsimp only [K]
    gcongr
  exact ⟨hMainK.trans (hLift hBaseMain (by positivity)),
    hLift hBaseNext (by positivity)⟩

/-- The complete logarithmic packet attached to an actual nonempty Type-II
colour.  It is the finite source object consumed by the subsequent
Heath--Brown algebra. -/
theorem eventually_actualTypeII_exponentPacket
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (hsigmaUpper : sigma <= 1)
    (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4) :
    ∀ᶠ U : Real in atTop,
      ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kII * 2)),
        binaryScaleLabel label.1 = Sum.inr r ->
        let N := classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1
        let p := heathBrownSourcePower N U
        let P := Nat.ceil (4 / delta2)
        let L := classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
        let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1
        ∀ full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ P : Real) * U) (2 * U + U ^ delta)
            N p eta L (classicalBinaryColorFamily d label) a
            Cp Cmv C0 C2 C4,
          (classicalBinaryColorFamily d label).Nonempty ->
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
          full.energy.Cp = Cp /\
            heathBrownEffectiveSigma sigma eta zetaShell zetaConst P - zetaDil <=
              sigmaMain /\
            heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1) -
                zetaDil <= sigmaNext /\
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
  let P := Nat.ceil (4 / delta2)
  obtain ⟨Uscale, _hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  obtain ⟨Ux, _hUx, hXfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta2 / 4) (b := delta2 / 2) (by positivity) (by linarith)
  obtain ⟨Uy, _hUy, hYfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta1 / 2) (b := delta1) (by positivity) (by linarith)
  have hThreshold := eventually_actualTypeII_commonThresholds
    (sigma := sigma) (delta := delta) hdelta1 hdelta2 hCube hsigmaUpper
    heta hzetaShell hzetaConst hzetaDil hC hCp
  have hLoss := eventually_heathBrown_finite_loss_le_power
    (P := P) (C2 := C2) (C4 := C4) hzetaRel hRelMargin hC0.le
  have hCardCoeff := eventually_heathBrown_cardinality_coefficients
    (P := P) hCmv hzetaCard
  filter_upwards [eventually_ge_atTop Uscale, eventually_ge_atTop Ux,
      eventually_ge_atTop Uy, hThreshold, hLoss, hCardCoeff,
      eventually_ge_atTop (1 : Real)]
    with U hUscaleU hUxU hUyU hThresholdU hLossU hCardCoeffU hU
  intro d label r hlabel
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
  have hScaleData := hScale U hUscaleU (by rw [d.hkII_eq]) label.1 r hlabel
  have hThresholdData := hThresholdU d label r hlabel
  dsimp only at hThresholdData
  dsimp only
  intro full hW
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
  have hNOne : 1 < N := by simpa only [N] using hScaleData.1
  have hN : 0 < N := by omega
  have hp : 3 <= p := by simpa only [N, p] using hScaleData.2.2.2.2.1
  have hpP : p <= P := by
    simpa only [N, p, P] using hScaleData.2.2.2.2.2.2.2.2
  have hBase : ((N ^ p : Nat) : Real) <= U := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.1
  have hNext : U <= ((N ^ (p + 1) : Nat) : Real) := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.2.1.le
  have hCubeMain : U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3 := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.2.2.1
  have hCoeffData := hCardCoeffU N p hN (by omega) hpP hCubeMain
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
        (Nat.le_mul_of_pos_left _
          (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hxNext : 1 < xNext := by
    dsimp only [xNext]
    exact_mod_cast (show 1 < 2 ^ P * N ^ (p + 1) by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
        (Nat.le_mul_of_pos_left _
          (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hV : 0 < V := by
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hx)
      (heathBrownEffectiveSigma sigma eta zetaShell zetaConst P - zetaDil)).trans_le
        hThresholdData.1
  have hVNext : 0 < VNext := by
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext)
      (heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1) -
        zetaDil)).trans_le hThresholdData.2
  have hCaps := full.common_cardinality_exponents
    (sigmaMain := sigmaMain) (sigmaNext := sigmaNext)
    hNOne hp hpP (zero_lt_one.trans_le hU) hCmv hW rfl hBase hNext
    hCubeMain
    (by
      exact le_of_eq (by simpa only [sigmaMain, x, V] using
        rpow_heathBrownLogExponent hx hV))
    (by
      exact le_of_eq (by simpa only [sigmaNext, xNext, VNext] using
        rpow_heathBrownLogExponent hxNext hVNext))
    hCoeffData.1 hCoeffData.2
  dsimp only at hCaps
  have hSigmaMain :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst P - zetaDil <=
        sigmaMain := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [sigmaMain, rpow_heathBrownLogExponent hx hV] using
      hThresholdData.1
  have hSigmaNext :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1) - zetaDil <=
        sigmaNext := by
    apply (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp
    simpa only [sigmaNext, rpow_heathBrownLogExponent hxNext hVNext] using
      hThresholdData.2
  have hLossSmall := hLossU N p hN (by omega) hpP hCubeMain
  have hSmallBase : ((2 ^ p * N ^ p : Nat) : Real) <= x := by
    dsimp only [x]
    exact_mod_cast Nat.mul_le_mul_right (N ^ p)
      (Nat.pow_le_pow_right (by omega) hpP)
  have hLossCommon :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          (((2 ^ P : Real) * U) ^ epsilon) <= x ^ zetaRel :=
    hLossSmall.trans (Real.rpow_le_rpow (by positivity) hSmallBase hzetaRel.le)
  have hRelation := full.logarithmic_relation_common hN (by omega)
    hpP (by
      have hXreal : (1 : Real) <= Nat.floor (U ^ (delta2 / 2)) := by
        calc
          1 <= U ^ (delta2 / 4) :=
            Real.one_le_rpow hU (by positivity)
          _ <= Nat.floor (U ^ (delta2 / 2)) := hXfloor U hUxU
      have hYreal : (1 : Real) <= Nat.floor (U ^ delta1) := by
        calc
          1 <= U ^ (delta1 / 2) :=
            Real.one_le_rpow hU (by positivity)
          _ <= Nat.floor (U ^ delta1) := hYfloor U hUyU
      exact classicalBinarySelectedThreshold_pos
        (by exact_mod_cast hYreal)
        (by exact_mod_cast hXreal)
        (by have := d.hkI; omega) (by have := d.hkII; omega)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) hC label.1)
    (by positivity) hC0.le hC2.le hC4.le hW
    (by simpa only [x] using hLossCommon)
  dsimp only at hRelation
  simpa only [x, xNext, V, VNext, E, sigmaMain, sigmaNext, tau, rho,
    rhoStar, P] using
    ⟨full.energy_Cp, hSigmaMain, hSigmaNext, hCaps.1, hCaps.2.1, hCaps.2.2.2.1,
      hCaps.2.2.2.2, hRelation⟩

#print axioms eventually_heathBrown_cardinality_coefficients
#print axioms eventually_actualTypeII_exponentPacket

end

end GafniTao
