import GafniTao.HeathBrownTypeIPoweredThreshold
import GafniTao.HeathBrownLongCommonThresholds

/-!
# Consecutive thresholds for an actual long Type-I colour

This is the source-faithful repair of the branch-independent threshold
estimate.  It uses the retained Type-I label to recover
`floor (U ^ delta1) <= N`, keeps the selected powers `p` and `p+1` exact,
and only then moves to the common dyadically dilated bases.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Effective real part for a genuine Type-I colour after exact-power
normalization and conversion through `U^(delta1/2) <= N`. -/
noncomputable def heathBrownTypeIEffectiveSigma
    (sigma delta1 delta2 eta zetaShell zetaConst : Real) : Real :=
  sigma - 2 * eta -
    (delta2 + zetaShell + zetaConst) / (delta1 / 2)

/-- The two consecutive common-base thresholds for an actual Type-I label
whose selected scale satisfies the source square condition. -/
theorem eventually_actualTypeI_long_commonThresholds
    {delta1 delta2 eta zetaShell zetaConst zetaDil C Cp : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hCp : 0 < Cp) :
    ∀ᶠ U : Real in atTop,
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kI * 2))
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
        binaryScaleLabel label.1 = Sum.inl r ->
        let N := classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1
        let p := heathBrownSourcePower N U
        let P := heathBrownLongPowerCap delta2
        let L := classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
        (((2 ^ P * N ^ p : Nat) : Real) ^
            (heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
              zetaShell zetaConst - zetaDil) <=
          heathBrownPoweredThreshold N p L Cp eta) /\
        (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^
            (heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
              zetaShell zetaConst - zetaDil) <=
          heathBrownPoweredThreshold N (p + 1) L Cp eta) := by
  let P := heathBrownLongPowerCap delta2
  have hSource := eventually_actualTypeI_selectedThreshold_lower
    (sigma := sigma) (delta := delta) (delta1 := delta1) (C := C)
    (delta2 := delta2) (eta := eta) (zeta := zetaShell) heta.le hzetaShell
  have hDenMain := eventually_const_le_rpow
    (D := Cp * (P : Real) * (2 : Real) ^ ((P : Real) * eta)) hzetaConst
  have hDenNext := eventually_const_le_rpow
    (D := Cp * ((P + 1 : Nat) : Real) *
      (2 : Real) ^ (((P + 1 : Nat) : Real) * eta)) hzetaConst
  obtain ⟨Uy, _hUy, hYfloor⟩ := eventually_rpow_le_natFloor_rpow
    (a := delta1 / 2) (b := delta1) (by positivity) (by linarith)
  have hD : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
  have hs : heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
      zetaShell zetaConst <= 1 := by
    unfold heathBrownTypeIEffectiveSigma
    have hLoss : 0 <= 2 * eta +
        (delta2 + zetaShell + zetaConst) / (delta1 / 2) := by positivity
    linarith
  have hCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ P) hD hs hzetaDil
  filter_upwards [hSource, hDenMain, hDenNext, hCommon,
      eventually_ge_atTop Uy, eventually_ge_atTop (1 : Real)]
    with U hSourceU hDenMainU hDenNextU hCommonU hUyU hU
  intro d label r out hlabel
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  have hN : 0 < N := by simpa only [N] using out.hN
  have hp : 0 < p := by
    have : 2 <= p := by simpa only [N, p] using out.scale.1
    omega
  have hpP : p <= P := by
    have hCap : p <= Nat.ceil (4 / delta2) := by
      simpa only [N, p] using out.scale.2.2.2.2
    dsimp only [P, heathBrownLongPowerCap]
    omega
  have hpNextP : p + 1 <= P + 1 := Nat.add_le_add_right hpP 1
  have hLowerY : Nat.floor (U ^ delta1) <= N := by
    simpa only [N, classicalBinarySelectedN, hlabel, Sum.elim_inl] using
      (le_classicalBinarySelectedN_of_typeI
        (Y := Nat.floor (U ^ delta1))
        (X := Nat.floor (U ^ (delta2 / 2))) label.1 r hlabel)
  have hLower : U ^ (delta1 / 2) <= (N : Real) := by
    calc
      U ^ (delta1 / 2) <= Nat.floor (U ^ delta1) := hYfloor U hUyU
      _ <= N := by exact_mod_cast hLowerY
  have hThreshold : U ^ (-(delta2 + zetaShell)) *
      (N : Real) ^ (sigma - eta) <= L := by
    simpa only [N, L] using hSourceU d label.1 r hlabel out.hN
  have hDenP : Cp * (p : Real) *
      (2 : Real) ^ ((p : Real) * eta) <= U ^ zetaConst :=
    (powered_normalization_denominator_le hCp.le heta.le hpP).trans hDenMainU
  have hDenNextP : Cp * ((p + 1 : Nat) : Real) *
      (2 : Real) ^ (((p + 1 : Nat) : Real) * eta) <= U ^ zetaConst :=
    (powered_normalization_denominator_le hCp.le heta.le hpNextP).trans
      hDenNextU
  have hMain := heathBrownTypeIPoweredThreshold_lower_on_power_scale
    hU hN hp heta (show 0 < delta1 / 2 by positivity)
      (add_nonneg hdelta2.le hzetaShell.le) hzetaConst.le hCp
      hThreshold hDenP hLower
  have hNext := heathBrownTypeIPoweredThreshold_lower_on_power_scale
    hU hN (by omega : 0 < p + 1) heta
      (show 0 < delta1 / 2 by positivity)
      (add_nonneg hdelta2.le hzetaShell.le) hzetaConst.le hCp
      hThreshold hDenNextP hLower
  have hMainScale : U ^ (2 : Nat) <=
      ((N ^ p : Nat) : Real) ^ (3 : Nat) := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.2.2.1
  have hPowMono : ((N ^ p : Nat) : Real) <=
      ((N ^ (p + 1) : Nat) : Real) := by
    exact_mod_cast (show N ^ p <= N ^ (p + 1) by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ hN)
  have hNextScale : U ^ (2 : Nat) <=
      ((N ^ (p + 1) : Nat) : Real) ^ (3 : Nat) :=
    hMainScale.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ p)) hMainScale
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ (p + 1))) hNextScale
  dsimp only
  constructor
  · have h := hCommonU ((N ^ p : Nat) : Real)
      (heathBrownPoweredThreshold N p L Cp eta) hU hLowerMain hMain
    simpa only [N, p, P, L, heathBrownTypeIEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h
  · have h := hCommonU ((N ^ (p + 1) : Nat) : Real)
      (heathBrownPoweredThreshold N (p + 1) L Cp eta)
      hU hLowerNext hNext
    simpa only [N, p, P, L, heathBrownTypeIEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h

#print axioms heathBrownTypeIEffectiveSigma
#print axioms eventually_actualTypeI_long_commonThresholds

end

end GafniTao
