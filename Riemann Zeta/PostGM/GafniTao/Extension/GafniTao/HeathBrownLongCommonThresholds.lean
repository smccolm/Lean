import GafniTao.HeathBrownLongSourceThreshold
import GafniTao.HeathBrownCommonThresholdExponent

/-!
# Common-base thresholds for every long detector colour

This module consumes the actual branch-independent long-colour output.  It
splits on the retained binary detector label, proves the appropriate source
threshold in each branch, powers at the source-selected exponent, and then
absorbs the fixed common-base dilation.  Thus no Type-I colour is relabelled
as Type II.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The effective powered exponent for the branch-independent long route.
The physical Type-I detector loss `delta2` is charged also in the Type-II
case so that both actual labels share one honest lower bound. -/
noncomputable def heathBrownLongEffectiveSigma
    (sigma delta2 eta zetaShell zetaConst : Real) (P : Nat) : Real :=
  sigma - 2 * eta -
    (3 / 2 : Real) * ((delta2 + zetaShell) * (P : Real) + zetaConst)

/-- Consecutive common-base threshold bounds attached to an actual long
detector-colour output. -/
theorem eventually_heathBrownLong_commonThresholds
    {delta1 delta2 eta zetaShell zetaConst zetaDil C Cp : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hC : 0 < C) (hCp : 0 < Cp) :
    ∀ᶠ U : Real in atTop,
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
        let N := classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1
        let p := heathBrownSourcePower N U
        let P := heathBrownLongPowerCap delta2
        let L := classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
        (((2 ^ P * N ^ p : Nat) : Real) ^
            (heathBrownLongEffectiveSigma sigma delta2 eta zetaShell
              zetaConst P - zetaDil) <=
          heathBrownPoweredThreshold N p L Cp eta) /\
        (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^
            (heathBrownLongEffectiveSigma sigma delta2 eta zetaShell
              zetaConst (P + 1) - zetaDil) <=
          heathBrownPoweredThreshold N (p + 1) L Cp eta) := by
  let P := heathBrownLongPowerCap delta2
  have hTotal : 0 < delta2 + zetaShell := add_pos hdelta2 hzetaShell
  have hTypeI := eventually_actualTypeI_selectedThreshold_lower
    (sigma := sigma) (delta := delta) (delta1 := delta1) (C := C)
    (delta2 := delta2) (eta := eta) (zeta := zetaShell) heta.le hzetaShell
  have hTypeII := eventually_typeII_selectedThreshold_lower
    (delta := delta1) (eta := eta) (zeta := delta2 + zetaShell)
      hdelta1 hTotal hC
  have hDenMain := eventually_const_le_rpow
    (D := Cp * (P : Real) * (2 : Real) ^ ((P : Real) * eta)) hzetaConst
  have hDenNext := eventually_const_le_rpow
    (D := Cp * ((P + 1 : Nat) : Real) *
      (2 : Real) ^ (((P + 1 : Nat) : Real) * eta)) hzetaConst
  have hD : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
  have hsMain :
      heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst P <= 1 := by
    unfold heathBrownLongEffectiveSigma
    have hLoss : 0 <= 2 * eta +
        (3 / 2 : Real) * ((delta2 + zetaShell) * (P : Real) + zetaConst) := by
      positivity
    linarith
  have hsNext :
      heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst
          (P + 1) <= 1 := by
    unfold heathBrownLongEffectiveSigma
    have hLoss : 0 <= 2 * eta +
        (3 / 2 : Real) *
          ((delta2 + zetaShell) * ((P + 1 : Nat) : Real) + zetaConst) := by
      positivity
    linarith
  have hCommonMain := eventually_common_base_threshold
    (D := (2 : Real) ^ P) hD hsMain hzetaDil
  have hCommonNext := eventually_common_base_threshold
    (D := (2 : Real) ^ P) hD hsNext hzetaDil
  filter_upwards [hTypeI, hTypeII, hDenMain, hDenNext,
      hCommonMain, hCommonNext, eventually_ge_atTop (1 : Real)]
    with U hTypeIU hTypeIIU hDenMainU hDenNextU hCommonMainU
      hCommonNextU hU
  intro d label out
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  have hN : 0 < N := by simpa only [N] using out.hN
  have hpTwo : 2 <= p := by simpa only [N, p] using out.scale.1
  have hp : 0 < p := by omega
  have hpCap : p <= Nat.ceil (4 / delta2) := by
    simpa only [N, p] using out.scale.2.2.2.2
  have hpP : p <= P := by
    dsimp only [P, heathBrownLongPowerCap]
    omega
  have hpNextP : p + 1 <= P + 1 := Nat.add_le_add_right hpP 1
  have hMainScale : U ^ (2 : Nat) <= ((N ^ p : Nat) : Real) ^ (3 : Nat) := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.2.2.1
  have hPowMono : ((N ^ p : Nat) : Real) <=
      ((N ^ (p + 1) : Nat) : Real) := by
    exact_mod_cast (show N ^ p <= N ^ (p + 1) by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ hN)
  have hNextScale : U ^ (2 : Nat) <=
      ((N ^ (p + 1) : Nat) : Real) ^ (3 : Nat) := by
    exact hMainScale.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hSource : U ^ (-(delta2 + zetaShell)) *
        (N : Real) ^ (sigma - eta) <= L := by
    cases hlabel : binaryScaleLabel label.1 with
    | inl r =>
        simpa only [N, L] using hTypeIU d label.1 r hlabel out.hN
    | inr r =>
        have hkII : d.kII <= Nat.clog 2 (Nat.floor (U ^ delta1)) := by
          rw [d.hkII_eq]
        have hkIIPos : 0 < d.kII := by
          have := d.hkII
          omega
        simpa only [N, L] using
          hTypeIIU (Nat.floor (U ^ delta1))
            (Nat.floor (U ^ (delta2 / 2))) d.kI d.kII sigma
            (U ^ (-delta2)) label.1 r hkII hkIIPos hlabel out.hN
  have hPoweredMain := heathBrownPoweredThreshold_lower_on_power_scale
    hU hN hp hpP heta hTotal.le hzetaConst.le hCp hSource hDenMainU hMainScale
  have hPoweredNext := heathBrownPoweredThreshold_lower_on_power_scale
    hU hN (by omega : 0 < p + 1) hpNextP heta hTotal.le hzetaConst.le hCp
      hSource hDenNextU hNextScale
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ p)) hMainScale
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ (p + 1))) hNextScale
  dsimp only
  constructor
  · have h := hCommonMainU ((N ^ p : Nat) : Real)
      (heathBrownPoweredThreshold N p L Cp eta) hU hLowerMain hPoweredMain
    simpa only [N, p, P, L, heathBrownLongEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow] using h
  · have h := hCommonNextU ((N ^ (p + 1) : Nat) : Real)
      (heathBrownPoweredThreshold N (p + 1) L Cp eta)
      hU hLowerNext hPoweredNext
    simpa only [N, p, P, L, heathBrownLongEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow] using h

#print axioms heathBrownLongEffectiveSigma
#print axioms eventually_heathBrownLong_commonThresholds

end

end GafniTao
