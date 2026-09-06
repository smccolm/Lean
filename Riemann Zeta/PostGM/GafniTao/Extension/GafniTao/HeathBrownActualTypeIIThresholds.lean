import GafniTao.HeathBrownCommonCardinalityPhysical
import GafniTao.HeathBrownPoweredThresholdLower

/-!
# Consecutive threshold bounds for an actual Type-II source label

The source power `p` and its companion `p+1` use one globally fixed
factorization constant.  This file applies the exact detector normalization
to both powers, retaining all shell and coefficient losses.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exponent left after the detector, coefficient, and finite-power
normalizations have been charged against a power bounded by `P`. -/
noncomputable def heathBrownEffectiveSigma
    (sigma eta zetaShell zetaConst : Real) (P : Nat) : Real :=
  sigma - 2 * eta -
    (3 / 2 : Real) * (zetaShell * (P : Real) + zetaConst)

/-- Both consecutive powered thresholds for an actual Type-II label.  The
second bound uses `P+1`; no uniformity in the power is inferred after the
constants have been selected. -/
theorem eventually_actualTypeII_consecutiveThresholds
    {delta1 delta2 eta zetaShell zetaConst C Cp : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hzetaShell : 0 < zetaShell)
    (hzetaConst : 0 < zetaConst) (hC : 0 < C) (hCp : 0 < Cp) :
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
        0 < N ∧ 3 ≤ p ∧ p ≤ P ∧
        U ^ (2 : Nat) ≤ ((N ^ p : Nat) : Real) ^ (3 : Nat) ∧
        U ^ (2 : Nat) ≤ ((N ^ (p + 1) : Nat) : Real) ^ (3 : Nat) ∧
        ((N ^ p : Nat) : Real) ^
            (heathBrownEffectiveSigma sigma eta zetaShell zetaConst P) ≤
          heathBrownPoweredThreshold N p
            (classicalBinarySelectedThreshold
              (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
              d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta ∧
        ((N ^ (p + 1) : Nat) : Real) ^
            (heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1)) ≤
          heathBrownPoweredThreshold N (p + 1)
            (classicalBinarySelectedThreshold
              (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
              d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta := by
  obtain ⟨Uscale, _hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  have hMain := eventually_typeII_poweredThreshold_lower_on_power_scale
    (delta := delta1) (eta := eta) (zetaShell := zetaShell)
    (zetaConst := zetaConst) (C := C) (Cp := Cp)
    (P := Nat.ceil (4 / delta2)) hdelta1 heta hzetaShell hzetaConst hC hCp
  have hNext := eventually_typeII_poweredThreshold_lower_on_power_scale
    (delta := delta1) (eta := eta) (zetaShell := zetaShell)
    (zetaConst := zetaConst) (C := C) (Cp := Cp)
    (P := Nat.ceil (4 / delta2) + 1) hdelta1 heta hzetaShell hzetaConst hC hCp
  filter_upwards [eventually_ge_atTop Uscale, hMain, hNext]
    with U hUscaleU hMainU hNextU
  intro d label r hlabel
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let P := Nat.ceil (4 / delta2)
  have hScaleData := hScale U hUscaleU (by rw [d.hkII_eq]) label.1 r hlabel
  have hNOne : 1 < N := by simpa only [N] using hScaleData.1
  have hN : 0 < N := by omega
  have hpThree : 3 ≤ p := by
    simpa only [N, p] using hScaleData.2.2.2.2.1
  have hp : 0 < p := by omega
  have hpP : p ≤ P := by
    simpa only [N, p, P] using hScaleData.2.2.2.2.2.2.2.2
  have hUOne : 1 ≤ U := by linarith [hScaleData.2.2.2.1]
  have hMainScale : U ^ (2 : Nat) ≤
      ((N ^ p : Nat) : Real) ^ (3 : Nat) := by
    simpa only [N, p, Nat.cast_pow] using
      hScaleData.2.2.2.2.2.2.2.1
  have hPowNat : N ^ p ≤ N ^ (p + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right (N ^ p) hN
  have hPowReal : ((N ^ p : Nat) : Real) ≤
      ((N ^ (p + 1) : Nat) : Real) := by exact_mod_cast hPowNat
  have hCubeMono : ((N ^ p : Nat) : Real) ^ (3 : Nat) ≤
      ((N ^ (p + 1) : Nat) : Real) ^ (3 : Nat) := by gcongr
  have hNextScale : U ^ (2 : Nat) ≤
      ((N ^ (p + 1) : Nat) : Real) ^ (3 : Nat) :=
    hMainScale.trans hCubeMono
  have hkII : d.kII ≤ Nat.clog 2 (Nat.floor (U ^ delta1)) := by
    rw [d.hkII_eq]
  have hkIIPos : 0 < d.kII := by
    have hProduct := d.hkII
    omega
  have hMainThreshold := hMainU
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) label.1 r p hUOne hkII
    hkIIPos hlabel hN hp hpP hMainScale
  have hNextThreshold := hNextU
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) label.1 r (p + 1) hUOne hkII
    hkIIPos hlabel hN (by omega)
      (by
        have hpNextP : p + 1 ≤ P + 1 := Nat.add_le_add_right hpP 1
        simpa only [P] using hpNextP)
      hNextScale
  refine ⟨hN, hpThree, hpP, hMainScale, hNextScale, ?_, ?_⟩
  · simpa only [N, p, P, heathBrownEffectiveSigma] using hMainThreshold
  · simpa only [N, p, P, heathBrownEffectiveSigma] using hNextThreshold

#print axioms heathBrownEffectiveSigma
#print axioms eventually_actualTypeII_consecutiveThresholds

end

end GafniTao
