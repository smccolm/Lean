import GafniTao.HeathBrownActualTypeIIThresholds
import GafniTao.HeathBrownFiniteLossAbsorption

/-!
# Threshold exponents at the common Heath--Brown base

The normalized detector threshold is initially a power of `N^p`, whereas
the common logarithmic base used by the moment relation is `2^P N^p`.
This file absorbs the fixed factor `2^P` with one explicit positive exponent
loss.  No equality between the two bases is asserted.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A fixed dilation of a source scale can be absorbed into any strictly
positive exponent margin.  The source lower bound `U^(2/3) <= y` is kept
explicit because it is the quantitative reason the dilation is harmless. -/
theorem eventually_common_base_threshold
    {D s zeta : Real} (hD : 1 <= D) (hs : s <= 1)
    (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      ∀ y V : Real, 1 <= U -> U ^ (2 / 3 : Real) <= y ->
        y ^ s <= V -> (D * y) ^ (s - zeta) <= V := by
  have hmargin : (0 : Real) < (2 / 3 : Real) * zeta := by positivity
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := D) (a := (0 : Real)) (b := (2 / 3 : Real) * zeta) hmargin
  filter_upwards [hAbsorb] with U hAbsorbU
  intro y V hU hUy hThreshold
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hUrootOne : 1 <= U ^ (2 / 3 : Real) :=
    Real.one_le_rpow hU (by norm_num)
  have hy : 1 <= y := hUrootOne.trans hUy
  have hy0 : 0 <= y := zero_le_one.trans hy
  have hDpower : D ^ (s - zeta) <= D := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hD (by linarith : s - zeta <= 1)
  have hyPower : y ^ (s - zeta) <= y ^ s :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hDsmall : D <= U ^ ((2 / 3 : Real) * zeta) := by
    simpa only [Real.rpow_zero, mul_one] using hAbsorbU
  have hRootPower : U ^ ((2 / 3 : Real) * zeta) <= y ^ zeta := by
    calc
      U ^ ((2 / 3 : Real) * zeta) =
          (U ^ (2 / 3 : Real)) ^ zeta :=
        Real.rpow_mul hUpos.le (2 / 3 : Real) zeta
      _ <= y ^ zeta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hUpos.le _) hUy hzeta.le
  have hProduct : D * y ^ (s - zeta) <= y ^ s := by
    calc
      D * y ^ (s - zeta) <= y ^ zeta * y ^ (s - zeta) :=
        mul_le_mul_of_nonneg_right (hDsmall.trans hRootPower)
          (Real.rpow_nonneg hy0 _)
      _ = y ^ s := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hy)]
        congr 1
        ring
  calc
    (D * y) ^ (s - zeta) = D ^ (s - zeta) * y ^ (s - zeta) :=
      Real.mul_rpow (zero_le_one.trans hD) hy0
    _ <= D * y ^ (s - zeta) :=
      mul_le_mul_of_nonneg_right hDpower (Real.rpow_nonneg hy0 _)
    _ <= y ^ s := hProduct
    _ <= V := hThreshold

/-- Both actual consecutive Type-II thresholds, rewritten at their common
dyadically dilated bases.  The dilation loss is displayed separately from
the detector, shell, and coefficient losses in `heathBrownEffectiveSigma`. -/
theorem eventually_actualTypeII_commonThresholds
    {delta1 delta2 eta zetaShell zetaConst zetaDil C Cp : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (hsigmaUpper : sigma <= 1)
    (heta : 0 < eta) (hzetaShell : 0 < zetaShell)
    (hzetaConst : 0 < zetaConst) (hzetaDil : 0 < zetaDil)
    (hC : 0 < C) (hCp : 0 < Cp) :
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
        (((2 ^ P * N ^ p : Nat) : Real) ^
            (heathBrownEffectiveSigma sigma eta zetaShell zetaConst P -
              zetaDil) <=
          heathBrownPoweredThreshold N p
            (classicalBinarySelectedThreshold
              (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
              d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta) /\
        (((2 ^ P * N ^ (p + 1) : Nat) : Real) ^
            (heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1) -
              zetaDil) <=
          heathBrownPoweredThreshold N (p + 1)
            (classicalBinarySelectedThreshold
              (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
              d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta) := by
  let P := Nat.ceil (4 / delta2)
  have hD : (1 : Real) <= (2 : Real) ^ P := one_le_pow₀ (by norm_num)
  have hsMain : heathBrownEffectiveSigma sigma eta zetaShell zetaConst P <= 1 := by
    unfold heathBrownEffectiveSigma
    have hLoss : 0 <= 2 * eta +
        (3 / 2 : Real) * (zetaShell * (P : Real) + zetaConst) := by positivity
    linarith
  have hsNext :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst (P + 1) <= 1 := by
    unfold heathBrownEffectiveSigma
    have hLoss : 0 <= 2 * eta +
        (3 / 2 : Real) *
          (zetaShell * ((P + 1 : Nat) : Real) + zetaConst) := by positivity
    linarith
  have hMainCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ P) hD hsMain hzetaDil
  have hNextCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ P) hD hsNext hzetaDil
  have hThresholds := eventually_actualTypeII_consecutiveThresholds
    (sigma := sigma) (delta := delta)
    hdelta1 hdelta2 hCube heta hzetaShell hzetaConst hC hCp
  filter_upwards [hMainCommon, hNextCommon, hThresholds,
      eventually_ge_atTop (1 : Real)]
    with U hMainU hNextU hThresholdU hU
  intro d label r hlabel
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  have hData := hThresholdU d label r hlabel
  dsimp only at hData
  dsimp only
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ p)) hData.2.2.2.1
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hU) (Nat.cast_nonneg (N ^ (p + 1)))
      hData.2.2.2.2.1
  constructor
  · have h := hMainU ((N ^ p : Nat) : Real)
      (heathBrownPoweredThreshold N p
        (classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta)
      hU hLowerMain hData.2.2.2.2.2.1
    simpa only [P, Nat.cast_mul, Nat.cast_pow] using h
  · have h := hNextU ((N ^ (p + 1) : Nat) : Real)
      (heathBrownPoweredThreshold N (p + 1)
        (classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta)
      hU hLowerNext hData.2.2.2.2.2.2
    simpa only [P, Nat.cast_mul, Nat.cast_pow] using h

#print axioms eventually_common_base_threshold
#print axioms eventually_actualTypeII_commonThresholds

end

end GafniTao
