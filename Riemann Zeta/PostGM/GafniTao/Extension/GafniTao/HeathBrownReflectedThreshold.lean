import GafniTao.HeathBrownInteriorReflectedScalar
import GafniTao.HeathBrownTypeIPoweredThreshold

/-!
# Reflected Type-I threshold at an enlarged physical height

The Poisson-reflected block has length `P = T^(1 / theta)`, while the
energy family lives in `[-3T,3T]`.  We enlarge the Heath--Brown height to
`B = T^beta`.  This file records the exact exponent comparison which turns
the literal reflected threshold into a source threshold at height `B`.
Every loss is an explicit parameter.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The natural reflected cutoff gives the exact reciprocal logarithmic
scale inequality, not merely its coarser `1 / (1/2+d)` consequence. -/
theorem reflected_dyadic_reciprocal_scale_le
    {T tau theta d : Real} {P M : Nat}
    (hT : 1 < T) (hP : 1 < P) (hPM : P <= M)
    (htheta : 0 < theta)
    (hTheta : theta = typeILogarithmicScale T P)
    (hMUpper : (M : Real) <= T ^ (1 + d - 1 / tau)) :
    1 / theta <= 1 + d - 1 / tau := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hScale : (P : Real) ^ theta = T := by
    rw [hTheta]
    exact rpow_typeILogarithmicScale_eq hTPos hP
  have hPEq : (P : Real) = T ^ (1 / theta) :=
    natCast_eq_rpow_inv_of_rpow_eq hP htheta hScale
  apply (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp
  rw [← hPEq]
  exact (by exact_mod_cast hPM : (P : Real) <= M).trans hMUpper

/-- The elementary exponent comparison behind the reflected source
threshold.  The nonnegative term
`(2 * sigma - 1) * (1 / tau - 1 / 2)` is retained mathematically but may be
discarded once `sigma >= 1/2` and `tau <= 2`. -/
theorem reflected_source_exponent_le
    {sigma tau theta Uscale d u beta zetaShell zetaConst loss eta : Real}
    (hsigma : 1 / 2 <= sigma) (htau : 0 < tau) (htauTwo : tau <= 2)
    (htheta : 0 < theta) (hthetaUpper : theta <= Uscale)
    (hbeta : 0 <= beta) (hzetaShell : 0 <= zetaShell)
    (hloss : 0 <= loss)
    (heta : 0 <= eta)
    (hdual : 1 / theta <= 1 + d - 1 / tau)
    (hbudget :
      u + d * (2 * sigma + 1) + beta * zetaShell + zetaConst <=
        (loss + eta) / Uscale) :
    -beta * zetaShell + (sigma - loss - eta) / theta <=
      1 / 2 - u - d * sigma + (sigma - 1) / tau - d - zetaConst := by
  have hsigmaNonneg : 0 <= sigma := by linarith
  have hLossEta : 0 <= loss + eta := add_nonneg hloss heta
  have hInvLower : (loss + eta) / Uscale <= (loss + eta) / theta := by
    exact div_le_div_of_nonneg_left hLossEta htheta hthetaUpper
  have hSigmaDual : sigma / theta <= sigma * (1 + d - 1 / tau) := by
    calc
      sigma / theta = sigma * (1 / theta) := by ring
      _ <= sigma * (1 + d - 1 / tau) :=
        mul_le_mul_of_nonneg_left hdual hsigmaNonneg
  have hTauMargin : 0 <=
      (2 * sigma - 1) * (1 / tau - 1 / 2) := by
    have hFirst : 0 <= 2 * sigma - 1 := by linarith
    have hSecond : 0 <= 1 / tau - 1 / 2 := by
      have := one_div_le_one_div_of_le htau htauTwo
      linarith
    positivity
  calc
    -beta * zetaShell + (sigma - loss - eta) / theta =
        sigma / theta - (loss + eta) / theta - beta * zetaShell := by
      ring
    _ <= sigma * (1 + d - 1 / tau) - (loss + eta) / Uscale -
        beta * zetaShell := by linarith
    _ <= sigma * (1 + d - 1 / tau) -
        (u + d * (2 * sigma + 1) + beta * zetaShell + zetaConst) -
        beta * zetaShell := by linarith
    _ <= 1 / 2 - u - d * sigma + (sigma - 1) / tau - d -
        zetaConst := by
      have hBeta : 0 <= 2 * beta * zetaShell := by positivity
      have hIdentity :
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - d -
              zetaConst) -
            (sigma * (1 + d - 1 / tau) -
              (u + d * (2 * sigma + 1) + beta * zetaShell + zetaConst) -
              beta * zetaShell) =
            (2 * sigma - 1) * (1 / tau - 1 / 2) +
              2 * beta * zetaShell := by ring
      have hDiff : 0 <=
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - d -
              zetaConst) -
            (sigma * (1 + d - 1 / tau) -
              (u + d * (2 * sigma + 1) + beta * zetaShell + zetaConst) -
              beta * zetaShell) := by
        rw [hIdentity]
        positivity
      linarith

/-- Exact conversion of a literal reflected threshold into the source
threshold used by the powered Heath--Brown machinery. -/
theorem reflected_source_threshold_on_expanded_height
    {T tau theta Uscale d u beta zetaShell zetaConst loss eta C L : Real}
    {P : Nat}
    (hT : 1 <= T) (hP : 1 < P)
    (hTheta : theta = typeILogarithmicScale T P)
    (hsigma : 1 / 2 <= sigma) (htau : 0 < tau) (htauTwo : tau <= 2)
    (htheta : 0 < theta) (hthetaUpper : theta <= Uscale)
    (hbeta : 0 <= beta) (hzetaShell : 0 <= zetaShell)
    (hloss : 0 <= loss)
    (heta : 0 <= eta)
    (hdual : 1 / theta <= 1 + d - 1 / tau)
    (hbudget :
      u + d * (2 * sigma + 1) + beta * zetaShell + zetaConst <=
        (loss + eta) / Uscale)
    (hC : 0 < C) (hCAbsorb : C <= T ^ zetaConst)
    (hLiteral :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) / C <= L) :
    (T ^ beta) ^ (-zetaShell) *
        (P : Real) ^ (sigma - loss - eta) <= L := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hThetaScale : (P : Real) ^ theta = T := by
    rw [hTheta]
    exact rpow_typeILogarithmicScale_eq hTPos hP
  have hPEq : (P : Real) = T ^ (1 / theta) :=
    natCast_eq_rpow_inv_of_rpow_eq hP htheta hThetaScale
  have hExponent := reflected_source_exponent_le hsigma htau htauTwo
    htheta hthetaUpper hbeta hzetaShell hloss heta hdual hbudget
  have hCInv : T ^ (-zetaConst) <= C⁻¹ := by
    rw [Real.rpow_neg hTPos.le]
    simpa only [one_div] using one_div_le_one_div_of_le hC hCAbsorb
  have hPower :
      T ^ (-beta * zetaShell + (sigma - loss - eta) / theta) <=
        T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d -
          zetaConst) :=
    Real.rpow_le_rpow_of_exponent_le hT hExponent
  calc
    (T ^ beta) ^ (-zetaShell) *
        (P : Real) ^ (sigma - loss - eta) =
      T ^ (-beta * zetaShell + (sigma - loss - eta) / theta) := by
        rw [hPEq, ← Real.rpow_mul hTPos.le, ← Real.rpow_mul hTPos.le,
          ← Real.rpow_add hTPos]
        congr 1
        ring
    _ <= T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d -
        zetaConst) := hPower
    _ = T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) *
        T ^ (-zetaConst) := by
      rw [← Real.rpow_add hTPos]
      congr 1
    _ <= T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) * C⁻¹ :=
      mul_le_mul_of_nonneg_left hCInv (Real.rpow_nonneg hTPos.le _)
    _ = T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) / C := by
      rfl
    _ <= L := hLiteral

/-- The expanded height `T^beta` contains the square of every reflected
dyadic length, and the literal logarithmic power choice is bounded by the
ceiling of `beta * Uscale`. -/
theorem reflected_dyadic_expanded_power_window
    {T tau theta Uscale d beta : Real} {P M : Nat}
    (hT : 1 < T) (hP : 1 < P) (hPM : P <= M)
    (hMUpper : (M : Real) <= T ^ (1 + d - 1 / tau))
    (hExponent : 2 * (1 + d - 1 / tau) <= beta)
    (hbeta : 0 < beta)
    (hTheta : theta = typeILogarithmicScale T P)
    (htheta : 0 < theta) (hthetaUpper : theta <= Uscale) :
    let B := T ^ beta
    let p := heathBrownSourcePower P B
    2 <= p /\ (P : Real) ^ p <= B /\ B < (P : Real) ^ (p + 1) /\
      B ^ 2 <= ((P : Real) ^ p) ^ 3 /\
      p <= Nat.ceil (beta * Uscale) := by
  dsimp only
  let B : Real := T ^ beta
  let p : Nat := heathBrownSourcePower P B
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hBPos : 0 < B := by dsimp only [B]; positivity
  have hPReal : (0 : Real) < P := by positivity
  have hPSquareM : (P : Real) ^ (2 : Nat) <= (M : Real) ^ (2 : Nat) := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg P) (by exact_mod_cast hPM) 2
  have hMSquare : (M : Real) ^ (2 : Nat) <=
      (T ^ (1 + d - 1 / tau)) ^ (2 : Nat) :=
    pow_le_pow_left₀ (Nat.cast_nonneg M) hMUpper 2
  have hExpanded : (T ^ (1 + d - 1 / tau)) ^ (2 : Nat) <= T ^ beta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT.le (by
      simpa only [Nat.cast_ofNat, mul_comm] using hExponent)
  have hSquare : (P : Real) ^ (2 : Nat) <= B := by
    dsimp only [B]
    exact hPSquareM.trans (hMSquare.trans hExpanded)
  have hSpec := heathBrownSourcePower_spec_two hP hBPos hSquare
  dsimp only at hSpec
  have hlogP : 0 < Real.log (P : Real) :=
    Real.log_pos (by exact_mod_cast hP)
  have hRatioEq : Real.log B / Real.log (P : Real) = beta * theta := by
    dsimp only [B]
    rw [Real.log_rpow hTPos]
    rw [hTheta]
    unfold typeILogarithmicScale Real.logb
    field_simp
  have hRatioNonneg : 0 <= Real.log B / Real.log (P : Real) := by
    rw [hRatioEq]
    positivity
  have hpReal : (p : Real) <= beta * Uscale := by
    calc
      (p : Real) <= Real.log B / Real.log (P : Real) := by
        simpa only [p, heathBrownSourcePower] using
          Nat.floor_le hRatioNonneg
      _ = beta * theta := hRatioEq
      _ <= beta * Uscale := mul_le_mul_of_nonneg_left hthetaUpper hbeta.le
  have hpCeil : p <= Nat.ceil (beta * Uscale) := by
    exact_mod_cast hpReal.trans (Nat.le_ceil (beta * Uscale))
  exact ⟨hSpec.1, hSpec.2.1, hSpec.2.2.1, hSpec.2.2.2, hpCeil⟩

/-- A uniform lower polynomial scale for the enlarged height. -/
theorem reflected_expanded_height_lower_scale
    {T theta Uscale beta : Real} {P : Nat}
    (hT : 1 < T) (hP : 1 < P)
    (hTheta : theta = typeILogarithmicScale T P)
    (htheta : 0 < theta) (hUscale : 0 < Uscale)
    (hthetaUpper : theta <= Uscale) (hbeta : 0 < beta) :
    (T ^ beta) ^ (1 / (beta * Uscale)) <= (P : Real) := by
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hScale : (P : Real) ^ theta = T := by
    rw [hTheta]
    exact rpow_typeILogarithmicScale_eq hTPos hP
  have hPEq : (P : Real) = T ^ (1 / theta) :=
    natCast_eq_rpow_inv_of_rpow_eq hP htheta hScale
  have hInv : 1 / Uscale <= 1 / theta := by
    exact one_div_le_one_div_of_le htheta hthetaUpper
  rw [← Real.rpow_mul hTPos.le, hPEq]
  apply Real.rpow_le_rpow_of_exponent_le hT.le
  field_simp [hbeta.ne', hUscale.ne']
  nlinarith

#print axioms reflected_source_exponent_le
#print axioms reflected_source_threshold_on_expanded_height
#print axioms reflected_dyadic_expanded_power_window
#print axioms reflected_dyadic_reciprocal_scale_le
#print axioms reflected_expanded_height_lower_scale

end

end GafniTao
