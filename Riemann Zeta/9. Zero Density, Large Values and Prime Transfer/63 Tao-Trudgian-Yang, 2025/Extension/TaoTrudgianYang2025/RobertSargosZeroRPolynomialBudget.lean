import TaoTrudgianYang2025.SecondDerivativeScale

/-! Physical polynomial budgets for the zero-r row, retaining all floor losses. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem zero_r_physical_polynomial_budgets {T M H Q R lam : ℝ}
    (hT : 2 ≤ T) (hM : T^8 ≤ M) (hH : 0 < H) (hHmax : H ≤ T^2/2)
    (hQmin : T^3/2 ≤ Q) (hQmax : Q ≤ T^3) (hR : T/2 ≤ R)
    (hlam : 0 < lam) (hscale : T^13*lam = 1) :
    4*H*Q*lam ≤ 1 ∧ H^2 ≤ M*R ∧
      H^5*Q*lam ≤ R^2 ∧ H^3 ≤ M^2*R^2*Q*lam := by
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hMp : 0 < M := (pow_pos hTp 8).trans_le hM
  have hQp : 0 < Q := lt_of_lt_of_le (by positivity) hQmin
  have hRp : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hT8 : 2 ≤ T^8 := hT.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hT1 (by norm_num : 1 ≤ 8))
  have hcurv : 4*H*Q*lam ≤ 1 := by
    have hprod := mul_le_mul hHmax hQmax hQp.le (by positivity : 0 ≤ T^2/2)
    have hprodLam := mul_le_mul_of_nonneg_right hprod hlam.le
    have hp := mul_le_mul_of_nonneg_right hT8 (show 0 ≤ T^5 by positivity)
    have hpLam := mul_le_mul_of_nonneg_right hp hlam.le
    nlinarith [hscale]
  have hdiag : H^2 ≤ M*R := by
    have hsq := pow_le_pow_left₀ hH.le hHmax 2
    have hp := pow_le_pow_right₀ hT1 (by norm_num : 4 ≤ 9)
    have hprod := mul_le_mul hM hR (by positivity : 0 ≤ T/2) hMp.le
    nlinarith
  have hpos : H^5*Q*lam ≤ R^2 := by
    have hpow := pow_le_pow_left₀ hH.le hHmax 5
    have hprod := mul_le_mul hpow hQmax hQp.le
      (show 0 ≤ (T^2/2)^5 by positivity)
    have hprodLam := mul_le_mul_of_nonneg_right hprod hlam.le
    have hR1 : 1 ≤ R := by linarith
    nlinarith [sq_nonneg (R-1)]
  have hinv : H^3 ≤ M^2*R^2*Q*lam := by
    have hpow := pow_le_pow_left₀ hH.le hHmax 3
    have h68 := pow_le_pow_right₀ hT1 (by norm_num : 6 ≤ 8)
    have hm2 := pow_le_pow_left₀ (by positivity : 0 ≤ T^8) hM 2
    have hr2 := pow_le_pow_left₀ (by positivity : 0 ≤ T/2) hR 2
    have hprod := mul_le_mul hm2 hr2 (sq_nonneg (T/2)) (sq_nonneg M)
    have hprodQ := mul_le_mul hprod hQmin
      (by positivity : 0 ≤ T^3/2) (mul_nonneg (sq_nonneg M) (sq_nonneg R))
    have hprodLam := mul_le_mul_of_nonneg_right hprodQ hlam.le
    have he : (T^8/8) = (T^8)^2*(T/2)^2*(T^3/2)*lam := by
      calc
        _ = (T^8/8)*(T^13*lam) := by rw [hscale,mul_one]
        _ = _ := by ring
    have hlow : T^8/8 ≤ M^2*R^2*Q*lam := he.trans_le hprodLam
    nlinarith
  exact ⟨hcurv,hdiag,hpos,hinv⟩

end TaoTrudgianYang2025
