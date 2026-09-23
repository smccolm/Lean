import TaoTrudgianYang2025.SargosCProcessMainBalance

/-! Controlled epsilon loss in the main term, using the exact unperturbed optimum. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_main_error_bound {k l ε D T N H : ℝ}
    (hk : 0 ≤ k) (hε : 0 ≤ ε) (hD : 0 < D) (hT : 0 < T) (hN : 0 < N) (hH : 0 < H)
    (hHR : H ≤ sargosCProcessScale k l T N) (hHN : H ≤ N) :
    N^11*(D*T*H^4/N^5)^(k+ε)*N^(l+ε) ≤
      D^(k+ε)*(N^12/sargosCProcessScale k l T N)*(T/N)^ε*N^ε := by
  let R := sargosCProcessScale k l T N
  let X := T*H^4/N^5
  have hR : 0 < R := sargosCProcessScale_pos hT hN
  have hX : 0 < X := by dsimp [X]; positivity
  have hXR : X ≤ T*R^4/N^5 := by
    dsimp [X]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le hHR 4) hT.le) (by positivity)
  have hXN : X ≤ T/N := by
    calc
      X ≤ T*N^4/N^5 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le hHN 4) hT.le) (by positivity)
      _ = _ := by field_simp
  have hbase : N^11*X^k*N^l ≤ N^12/R := by
    calc
      _ ≤ N^11*(T*R^4/N^5)^k*N^l :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hX.le hXR hk) (by positivity))
          (by positivity)
      _ = _ := sargosCProcess_main_balance hk hT hN
  have herror := Real.rpow_le_rpow hX.le hXN hε
  have heq : N^11*(D*T*H^4/N^5)^(k+ε)*N^(l+ε) =
      D^(k+ε)*(N^11*X^k*N^l)*X^ε*N^ε := by
    rw [show D*T*H^4/N^5 = D*X by dsimp [X]; ring,
      Real.mul_rpow hD.le hX.le,Real.rpow_add hX,Real.rpow_add hN]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hbase (by positivity)) herror
      (by positivity) (by positivity)) (by positivity)

theorem sargosCProcess_epsilon_budget {U N ε : ℝ}
    (hU : 1 ≤ U) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    U^ε*N^(2*ε) ≤ (U^ε*N^ε)^12 := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hu := Real.rpow_le_rpow_of_exponent_le hU (show ε ≤ ε*12 by linarith)
  have hn := Real.rpow_le_rpow_of_exponent_le hN (show 2*ε ≤ ε*12 by linarith)
  calc
    _ ≤ U^(ε*12)*N^(ε*12) := mul_le_mul hu hn (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast hUp.le,← Real.rpow_mul_natCast hNp.le]
      norm_num

end TaoTrudgianYang2025
