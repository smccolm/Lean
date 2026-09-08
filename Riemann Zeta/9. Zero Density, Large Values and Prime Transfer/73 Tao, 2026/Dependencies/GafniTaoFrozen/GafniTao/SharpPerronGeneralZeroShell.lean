import GafniTao.SharpPerronGeneralPsiAssembly
import GafniTao.SharpPerronZeroShell

/-!
# Transfer from the selected height to the requested height

This is the arbitrary-real-endpoint form of the zero-shell argument.  The
shell is the literal difference of the two multiplicity-weighted zero sets.
-/

namespace GafniTao

/-- The complete sharp explicit formula at every requested height in the
high-height range `8 ≤ T ≤ x`. -/
theorem exists_norm_sharpPsiTruncationError_general_high_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x : ℝ}, 8 ≤ T → T ≤ x →
      ‖sharpPsiTruncationError T x‖ ≤
        C * x * Real.log x ^ 2 / T := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_good_height_norm_sharpPsiTruncationError_general_le
  let D : ℝ := C + 16 * globalLocalZeroLogConstant
  refine ⟨D, by
    dsimp [D]
    exact add_pos hC (mul_pos (by norm_num) globalLocalZeroLogConstant_pos), ?_⟩
  intro T x hT hTx
  obtain ⟨R, hR, hRbound⟩ := hselected hT hTx
  have hxPos : 0 < x := by linarith [hT, hTx]
  have hTpos : 0 < T := by linarith
  have hlogTx : Real.log (T + 2) ≤ 2 * Real.log x := by
    have hT2pos : 0 < T + 2 := by linarith
    have hT2x2 : T + 2 ≤ x ^ 2 := by
      nlinarith [sq_nonneg (x - 1)]
    calc
      Real.log (T + 2) ≤ Real.log (x ^ 2) :=
        Real.log_le_log hT2pos hT2x2
      _ = 2 * Real.log x := by
        rw [show x ^ 2 = x ^ (2 : ℝ) by
          exact (Real.rpow_natCast x 2).symm, Real.log_rpow hxPos]
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hlogTwo : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by linarith [hT, hTx])
    linarith [Real.log_two_gt_d9]
  have hlogAbsorb : Real.log x ≤ 2 * Real.log x ^ 2 := by
    nlinarith [sq_nonneg (Real.log x)]
  have hshell := norm_sharpPerronShellZeroSum_le (y := x) hT hR
    (by linarith [hT, hTx])
  have hshell' : ‖sharpPerronShellZeroSum T R x‖ ≤
      16 * globalLocalZeroLogConstant * x * Real.log x ^ 2 / T := by
    calc
      _ ≤ 4 * globalLocalZeroLogConstant * Real.log (T + 2) *
          (x / T) := hshell
      _ ≤ 4 * globalLocalZeroLogConstant * (2 * Real.log x) *
          (x / T) := by
        have hcoeff : 0 ≤ 4 * globalLocalZeroLogConstant :=
          mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogTx hcoeff)
          (div_nonneg hxPos.le hTpos.le)
      _ ≤ 16 * globalLocalZeroLogConstant * x * Real.log x ^ 2 / T := by
        calc
          4 * globalLocalZeroLogConstant * (2 * Real.log x) * (x / T) =
              (8 * globalLocalZeroLogConstant * x / T) * Real.log x := by ring
          _ ≤ (8 * globalLocalZeroLogConstant * x / T) *
                (2 * Real.log x ^ 2) := by
            exact mul_le_mul_of_nonneg_left hlogAbsorb
              (div_nonneg
                (mul_nonneg
                  (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le)
                  hxPos.le) hTpos.le)
          _ = 16 * globalLocalZeroLogConstant * x * Real.log x ^ 2 / T := by
            ring
  rw [sharpPsiTruncationError_eq_selected_sub_shell (by linarith [hT]) hR.1]
  calc
    ‖sharpPsiTruncationError R x - sharpPerronShellZeroSum T R x‖ ≤
        ‖sharpPsiTruncationError R x‖ +
          ‖sharpPerronShellZeroSum T R x‖ := norm_sub_le _ _
    _ ≤ C * x * Real.log x ^ 2 / T +
          16 * globalLocalZeroLogConstant * x * Real.log x ^ 2 / T :=
      add_le_add hRbound hshell'
    _ = D * x * Real.log x ^ 2 / T := by
      dsimp [D]
      ring

end GafniTao
