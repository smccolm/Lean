import TaoTrudgianYang2025.ThirdDerivativeRpowScale

/-! The source's one-seventh and eight-thirteenths scales imply the small-block budgets. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_small_block_parameters {M H lam : ℝ}
    (hH : 0 ≤ H) (hlam : 0 < lam) (hlamSmall : lam ≤ 1/16)
    (hHM : H ≤ lam^(-(1:ℝ)/7)) (hM : lam^(-(8:ℝ)/13) ≤ M) :
    H ≤ M ∧ 4*H*lam ≤ 1 ∧ H^7*lam ≤ 1 ∧ H^5 ≤ M^3*lam := by
  have hlam1 : lam ≤ 1 := by linarith
  have hHtoM := Real.rpow_le_rpow_of_exponent_ge hlam hlam1
    (show -(8:ℝ)/13 ≤ -(1:ℝ)/7 by norm_num)
  have hfirst : H^7*lam ≤ 1 := by
    calc
      _ ≤ (lam^(-(1:ℝ)/7))^7*lam :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH hHM 7) hlam.le
      _ = 1 := by
        rw [← Real.rpow_mul_natCast hlam.le]
        norm_num
        rw [Real.rpow_neg_one,inv_mul_cancel₀ hlam.ne']
  have hsecond : H^5 ≤ M^3*lam := by
    calc
      _ ≤ (lam^(-(1:ℝ)/7))^5 := pow_le_pow_left₀ hH hHM 5
      _ = lam^(-(5:ℝ)/7) := by
        rw [← Real.rpow_mul_natCast hlam.le]
        congr 1
        norm_num
      _ ≤ lam^(-(11:ℝ)/13) :=
        Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by norm_num)
      _ = (lam^(-(8:ℝ)/13))^3*lam := by
        rw [← Real.rpow_mul_natCast hlam.le]
        have he := Real.rpow_add hlam ((-(8:ℝ)/13)*3) 1
        rw [Real.rpow_one] at he
        convert he using 1; norm_num
      _ ≤ M^3*lam := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg hlam.le _) hM 3) hlam.le
  have hs : H*lam ≤ Real.sqrt lam := by
    calc
      _ ≤ lam^(-(1:ℝ)/7)*lam := mul_le_mul_of_nonneg_right hHM hlam.le
      _ = lam^((6:ℝ)/7) := by
        have he := Real.rpow_add hlam (-(1:ℝ)/7) 1
        rw [Real.rpow_one] at he
        convert he.symm using 1; norm_num
      _ ≤ lam^((1:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by norm_num)
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hsqrt : Real.sqrt lam ≤ 1/4 := by
    nlinarith [Real.sq_sqrt hlam.le,Real.sqrt_nonneg lam]
  exact ⟨hHM.trans (hHtoM.trans hM),by linarith,hfirst,hsecond⟩

end TaoTrudgianYang2025
