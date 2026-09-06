import GafniTao.HeathBrownMHHExponent
import GafniTao.HeathBrownActualExponentPacket

/-!
# High-line MHH exponent cap for an actual Type-II colour

This theorem composes the real detector colour, the source power selected
from its physical scale, its actual normalized powered block, and the frozen
MHH theorem.  Every finite loss remains visible.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The actual high-line cardinality cap.  `zetaMHH` absorbs the fixed
power-selection and MHH constants; `3*epsilonMHH/2` is the uniform cost of
`B^epsilonMHH` because the source scale satisfies `tau <= 3/2`. -/
theorem eventually_actualTypeII_mhhExponentCap
    {delta1 delta2 eta epsilon epsilonMHH zetaMHH C Cp Cmhh : Real}
    (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (hepsilonMHH : 0 < epsilonMHH)
    (hzetaMHH : 0 < zetaMHH)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmhh : 0 < Cmhh)
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
      ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kII * 2)),
        binaryScaleLabel label.1 = Sum.inr r →
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
          (classicalBinaryColorFamily d label).Nonempty →
          let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
          let V := heathBrownPoweredThreshold N p L Cp eta
          let sigmaMain := heathBrownLogExponent x V
          let tau := heathBrownLogExponent x ((2 ^ P : Real) * U)
          let rho := heathBrownLogExponent x
            ((classicalBinaryColorFamily d label).card : Real)
          full.card.Cp = Cp ∧
            rho ≤ zetaMHH + (3 / 2 : Real) * epsilonMHH +
              max (2 - 2 * sigmaMain) (tau + 4 - 6 * sigmaMain) := by
  let P := Nat.ceil (4 / delta2)
  obtain ⟨Uscale, _hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  obtain ⟨Ux, _hUx, hXfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta2 / 4) (b := delta2 / 2) (by positivity) (by linarith)
  obtain ⟨Uy, _hUy, hYfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta1 / 2) (b := delta1) (by positivity) (by linarith)
  have hCoeff := eventually_heathBrown_cardinality_coefficients
    (P := P) hCmhh hzetaMHH
  filter_upwards [eventually_ge_atTop Uscale, eventually_ge_atTop Ux,
      eventually_ge_atTop Uy, hCoeff, eventually_ge_atTop (1 : Real)]
    with U hUscaleU hUxU hUyU hCoeffU hU
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
  dsimp only
  intro full hW
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let sigmaMain := heathBrownLogExponent x V
  let tau := heathBrownLogExponent x ((2 ^ P : Real) * U)
  let rho := heathBrownLogExponent x
    ((classicalBinaryColorFamily d label).card : Real)
  have hNOne : 1 < N := by simpa only [N] using hScaleData.1
  have hN : 0 < N := by omega
  have hp : 3 ≤ p := by simpa only [N, p] using hScaleData.2.2.2.2.1
  have hpP : p ≤ P := by
    simpa only [N, p, P] using hScaleData.2.2.2.2.2.2.2.2
  have hBase : ((N ^ p : Nat) : Real) ≤ U := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.1
  have hCubeMain : U ^ 2 ≤ ((N ^ p : Nat) : Real) ^ 3 := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.2.2.1
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
        (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hL : 0 < L := by
    have hXreal : (1 : Real) ≤ Nat.floor (U ^ (delta2 / 2)) := by
      calc
        1 ≤ U ^ (delta2 / 4) := Real.one_le_rpow hU (by positivity)
        _ ≤ Nat.floor (U ^ (delta2 / 2)) := hXfloor U hUxU
    have hYreal : (1 : Real) ≤ Nat.floor (U ^ delta1) := by
      calc
        1 ≤ U ^ (delta1 / 2) := Real.one_le_rpow hU (by positivity)
        _ ≤ Nat.floor (U ^ delta1) := hYfloor U hUyU
    exact classicalBinarySelectedThreshold_pos
      (by exact_mod_cast hYreal) (by exact_mod_cast hXreal)
      (by have := d.hkI; omega) (by have := d.hkII; omega)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) hC label.1
  have hPowThree : (8 : Real) ≤ (2 : Real) ^ P := by
    have hNat : 2 ^ 3 ≤ 2 ^ P := Nat.pow_le_pow_right (by omega) (hp.trans hpP)
    exact_mod_cast hNat
  have hShift : U ^ delta ≤ U := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU hdeltaUpper.le
  have hRB : 2 * (2 * U + U ^ delta) ≤ (2 ^ P : Real) * U := by
    calc
      2 * (2 * U + U ^ delta) ≤ 8 * U := by nlinarith
      _ ≤ (2 : Real) ^ P * U :=
        mul_le_mul_of_nonneg_right hPowThree (by positivity)
  have hRaw := full.card_le_mhh_common hCmhh.le hMHH hU hN (by omega)
    hpP (by simpa only [Nat.cast_pow] using hBase) hL hRB
    (classicalBinaryColorFamily_separated d label)
    (classicalBinaryColorFamily_in_symmetric_shell d label)
  have hV : 0 < V := by
    dsimp only [V, heathBrownPoweredThreshold]
    have hpR : (0 : Real) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hCardNat : 0 < (classicalBinaryColorFamily d label).card :=
    Finset.card_pos.mpr hW
  have hCard : (0 : Real) < (classicalBinaryColorFamily d label).card := by
    exact_mod_cast hCardNat
  have hBpos : 0 < (2 ^ P : Real) * U := by positivity
  have hBPower : x ^ tau = (2 ^ P : Real) * U := by
    exact rpow_heathBrownLogExponent hx hBpos
  have hThreshold : x ^ sigmaMain ≤ V := by
    exact le_of_eq (rpow_heathBrownLogExponent hx hV)
  have hCoeffData := hCoeffU N p hN (by omega) hpP hCubeMain
  have hCoeffP : 2 * ((p : Real) * Cmhh) ≤ x ^ zetaMHH := by
    have hpPReal : (p : Real) ≤ P := by exact_mod_cast hpP
    have hPC : (p : Real) * Cmhh ≤ P * Cmhh :=
      mul_le_mul_of_nonneg_right hpPReal hCmhh.le
    exact (mul_le_mul_of_nonneg_left hPC (by norm_num)).trans
      (by simpa only [x, Nat.cast_mul, Nat.cast_pow] using hCoeffData.1)
  have hLog := heathBrown_mhh_card_log_le hx hBpos hCard
    (mul_nonneg (Nat.cast_nonneg p) hCmhh.le) hThreshold hBPower
    (by
      simpa only [x, V, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hRaw)
    hCoeffP
  have hTauUpper : tau ≤ 3 / 2 := by
    have hScaleLog := heathBrown_common_logarithmic_scale
      (zero_lt_one.trans_le hU) hN (by omega) hpP hBase hCubeMain
    dsimp only at hScaleLog
    simpa only [tau, x, Nat.cast_mul, Nat.cast_pow] using hScaleLog.2.2
  refine ⟨full.card_Cp, ?_⟩
  dsimp only [rho, sigmaMain, tau] at hLog ⊢
  nlinarith

#print axioms eventually_actualTypeII_mhhExponentCap

end

end GafniTao
