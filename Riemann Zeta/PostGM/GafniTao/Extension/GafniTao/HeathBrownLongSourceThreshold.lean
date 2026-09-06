import GafniTao.ClassicalBinaryFullyUniformLongSource
import GafniTao.HeathBrownPoweredThresholdLower

/-!
# Threshold lower bounds for long source colours

For a selected Type-I colour the detector threshold contains the physical
factor `U ^ (-delta2)` and one sharp-zeta dyadic-shell denominator.  This
module absorbs only that denominator, keeps the physical loss explicit, and
then places the powered threshold on the same scale as the fully uniform
energy output.  The Type-II branch continues to use its separate normalized
threshold theorem.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Any fixed multiple of the number of sharp-zeta dyadic blocks is
eventually bounded by an arbitrary positive height power. -/
theorem eventually_const_mul_sharp_cutoff_clog_le_rpow
    {D zeta : Real} (hD : 0 <= D) (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) <= U ^ zeta := by
  let K : Real := 1 + (Real.log 6 + 1) / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 <= K := by
    dsimp only [K]
    positivity
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := D * K) (p := 1) (q := zeta) (b := 1)
    (mul_nonneg hD hK) hzeta (by norm_num)
  filter_upwards [hSmall, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (8 : Real)] with U hSmallU hExp hEight
  have hUPos : 0 < U := (Real.exp_pos 1).trans_le hExp
  have hLogOne : 1 <= Real.log U := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hClog := sharp_cutoff_clog_le_log_majorant U hEight
  have hMajorant :
      1 + (Real.log 6 + Real.log U) / Real.log 2 <=
        K * Real.log U := by
    dsimp only [K]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hInv : 0 <= (Real.log 2)⁻¹ := inv_nonneg.mpr hlogTwo.le
    nlinarith [mul_le_mul_of_nonneg_left hLogOne
      (mul_nonneg (Real.log_nonneg (by norm_num : (1 : Real) <= 6)) hInv)]
  have hFront :
      D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) <=
        (D * K) * Real.log U := by
    calc
      D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) <=
          D * (1 + (Real.log 6 + Real.log U) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hClog hD
      _ <= D * (K * Real.log U) :=
        mul_le_mul_of_nonneg_left hMajorant hD
      _ = (D * K) * Real.log U := by ring
  have hCancel : U ^ zeta * U ^ (-zeta) = 1 := by
    rw [← Real.rpow_add hUPos]
    norm_num
  have hScaled :
      D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) * U ^ (-zeta) <=
        1 := by
    calc
      D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) *
          U ^ (-zeta) <=
          ((D * K) * Real.log U) * U ^ (-zeta) :=
        mul_le_mul_of_nonneg_right hFront (Real.rpow_nonneg hUPos.le _)
      _ <= 1 := by simpa only [Real.rpow_one] using hSmallU
  calc
    D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) =
        (D * (Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) : Real) *
          U ^ (-zeta)) * U ^ zeta := by
      rw [mul_assoc, mul_comm (U ^ (-zeta)) (U ^ zeta),
        ← Real.rpow_add hUPos]
      norm_num
    _ <= 1 * U ^ zeta :=
      mul_le_mul_of_nonneg_right hScaled (Real.rpow_nonneg hUPos.le _)
    _ = U ^ zeta := one_mul _

/-- The exact selected Type-I threshold, with its physical detector loss and
sharp-zeta dyadic-shell denominator both visible. -/
theorem eventually_actualTypeI_selectedThreshold_lower
    {sigma delta delta1 C delta2 eta zeta : Real}
    (heta : 0 <= eta) (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (q : Fin (d.kI * 2 + d.kII * 2)) (r : Fin (d.kI * 2)),
        binaryScaleLabel q = Sum.inl r ->
        0 < classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII q ->
        U ^ (-(delta2 + zeta)) *
            (classicalBinarySelectedN
              (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
              d.kI d.kII q : Real) ^ (sigma - eta) <=
          classicalBinarySelectedThreshold
            (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
            d.kI d.kII sigma (U ^ (-delta2)) eta C q := by
  have hAbsorb := eventually_const_mul_sharp_cutoff_clog_le_rpow
    (D := (8 / 3 : Real)) (zeta := zeta) (by norm_num) hzeta
  filter_upwards [hAbsorb, eventually_ge_atTop (8 : Real)]
    with U hAbsorbU hU
  intro d q r hq hN
  have hUPos : 0 < U := by linarith
  have hUOne : 1 <= U := by linarith
  have hkI : d.kI = Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) := d.hkI_eq
  have hkIPos : 0 < d.kI := by
    have := d.hkI
    omega
  have hkIReal : (0 : Real) < d.kI := by exact_mod_cast hkIPos
  have hLoss : (8 / 3 : Real) * (d.kI : Real) <= U ^ zeta := by
    simpa only [hkI] using hAbsorbU
  have hCoeff : U ^ (-zeta) <= (3 / 8 : Real) / (d.kI : Real) := by
    rw [Real.rpow_neg hUPos.le]
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hUPos zeta) hkIReal).2
    have : (d.kI : Real) <= (3 / 8 : Real) * U ^ zeta := by
      nlinarith
    simpa only [one_mul] using this
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII q
  have hNOne : (1 : Real) <= N := by exact_mod_cast hN
  have hNPower : (N : Real) ^ (sigma - eta) <= (N : Real) ^ sigma :=
    Real.rpow_le_rpow_of_exponent_le hNOne (by linarith)
  have hNeq : N = classicalTypeIShellScaleN (Nat.floor (U ^ delta1)) r := by
    dsimp only [N, classicalBinarySelectedN]
    simp only [hq, Sum.elim_inl]
  rw [classicalBinarySelectedThreshold]
  simp only [hq, Sum.elim_inl]
  change U ^ (-(delta2 + zeta)) * (N : Real) ^ (sigma - eta) <= _
  have hHeight : U ^ (-(delta2 + zeta)) = U ^ (-delta2) * U ^ (-zeta) := by
    rw [← Real.rpow_add hUPos]
    congr 1
    ring
  rw [hHeight]
  calc
    U ^ (-delta2) * U ^ (-zeta) * (N : Real) ^ (sigma - eta) <=
        U ^ (-delta2) * ((3 / 8 : Real) / (d.kI : Real)) *
          (N : Real) ^ sigma := by
      gcongr
    _ = (N : Real) ^ sigma *
        (((3 / 4 : Real) * (U ^ (-delta2) / 2)) / (d.kI : Real)) := by
      field_simp [hkIReal.ne']
      ring
    _ = (classicalTypeIShellScaleN (Nat.floor (U ^ delta1)) r : Real) ^ sigma *
        (((3 / 4 : Real) * (U ^ (-delta2) / 2)) / (d.kI : Real)) := by
      rw [hNeq]

#print axioms eventually_const_mul_sharp_cutoff_clog_le_rpow
#print axioms eventually_actualTypeI_selectedThreshold_lower

end

end GafniTao
