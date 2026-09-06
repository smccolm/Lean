import GafniTao.HeathBrownBoundedCells

/-!
# Absorbing the logarithmic zero-shell cover

The global four-zero cover contributes the literal fourth power of
`dyadicZeroShellCount`.  This file proves that this exact natural-valued
factor is subpolynomial, including the `Nat.ceil` and base-two `Nat.log`
comparisons.
-/

open Asymptotics Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem dyadicZeroShellCount_isBigO_log :
    (fun T : Real => (dyadicZeroShellCount T : Real)) =O[atTop]
      Real.log := by
  let C : Real := 1 / Real.log 2 + 3
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with T hT
  have hTPos : 0 < T := (Real.exp_pos 2).trans_le hT
  have hTOne : 1 ≤ T := by
    have : 1 < Real.exp 2 := by simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (by norm_num : (0 : Real) < 2))
    exact this.le.trans hT
  have hCeilOne : 1 ≤ Nat.ceil T := by
    exact_mod_cast hTOne.trans (Nat.le_ceil T)
  have hCeilUpper : (Nat.ceil T : Real) ≤ 2 * T := by
    have hRaw := Nat.ceil_lt_add_one hTPos.le
    linarith
  have hLogCeil := natCast_log_two_le_log (Nat.ceil T) hCeilOne
  have hLogMono : Real.log (Nat.ceil T : Real) ≤ Real.log (2 * T) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Nat.ceil T by omega)
    · exact hCeilUpper
  have hLogMul : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hTPos.ne']
  have hLogT : 2 ≤ Real.log T := by
    exact (Real.le_log_iff_exp_le hTPos).mpr hT
  have hLogCeil' :
      Real.log (Nat.ceil T : Real) ≤ Real.log 2 + Real.log T := by
    rw [← hLogMul]
    exact hLogMono
  have hCount : (dyadicZeroShellCount T : Real) ≤ C * Real.log T := by
    unfold dyadicZeroShellCount
    push_cast
    dsimp only [C]
    calc
      (Nat.log 2 (Nat.ceil T) : Real) + 2 ≤
          Real.log (Nat.ceil T : Real) / Real.log 2 + 2 := by linarith
      _ ≤ (Real.log 2 + Real.log T) / Real.log 2 + 2 := by
        exact add_le_add_left (div_le_div_of_nonneg_right hLogCeil' hlogTwo.le) 2
      _ ≤ (1 / Real.log 2 + 3) * Real.log T := by
        rw [add_div, div_self hlogTwo.ne']
        field_simp [hlogTwo.ne']
        nlinarith [hLogT, hlogTwo]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by linarith)]
  exact hCount

/-- The fourth power of the exact cover count is absorbed by any positive
power. -/
theorem dyadicZeroShellCount_pow_four_isBigO_rpow
    {eps : Real} (heps : 0 < eps) :
    (fun T : Real => (dyadicZeroShellCount T : Real) ^ 4) =O[atTop]
      (fun T : Real => T ^ eps) := by
  have heighth : 0 < eps / 4 := by positivity
  have hBase :
      (fun T : Real => (dyadicZeroShellCount T : Real)) =O[atTop]
        (fun T : Real => T ^ (eps / 4)) :=
    dyadicZeroShellCount_isBigO_log.trans
      (isLittleO_log_rpow_atTop heighth).isBigO
  have hPow := hBase.pow 4
  apply hPow.congr' (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  rw [← Real.rpow_mul_natCast hT.le (eps / 4) 4]
  congr 1
  ring

/-- Multiplying by the exact fourth-power shell count preserves an
epsilon-exponent bound. -/
theorem EpsilonExponentBound.dyadic_shell_four_loss
    {f : Real → Real} {a : Real} (h : EpsilonExponentBound f a) :
    EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 * f T) a := by
  unfold EpsilonExponentBound at h ⊢
  intro eps heps
  have hepsHalf : 0 < eps / 2 := by positivity
  have hShell := dyadicZeroShellCount_pow_four_isBigO_rpow hepsHalf
  have hF := h (eps / 2) hepsHalf
  have hProduct := hShell.mul hF
  apply hProduct.congr' (Filter.Eventually.of_forall fun _ => by
    rw [abs_mul]
    simp only [abs_of_nonneg (by positivity :
      0 ≤ (dyadicZeroShellCount _ : Real) ^ 4)])
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  calc
    T ^ (eps / 2) * (T ^ (eps / 2) * |T ^ a|) =
        T ^ eps * |T ^ a| := by
      rw [← mul_assoc, ← Real.rpow_add hT]
      congr 2
      ring

#print axioms dyadicZeroShellCount_isBigO_log
#print axioms dyadicZeroShellCount_pow_four_isBigO_rpow
#print axioms EpsilonExponentBound.dyadic_shell_four_loss

end

end GafniTao
