import TaoTrudgianYang2025.SargosCProcessScale

/-! The main finite-process term at the actual optimizing physical scale. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_main_balance {k l T N : ℝ}
    (hk : 0 ≤ k) (hT : 0 < T) (hN : 0 < N) :
    N^11*(T*(sargosCProcessScale k l T N)^4/N^5)^k*N^l =
      N^12/sargosCProcessScale k l T N := by
  let R := sargosCProcessScale k l T N
  have hR : 0 < R := sargosCProcessScale_pos hT hN
  have hbal := sargosCProcessScale_balance (l := l) hk hT hN
  have hpow : (T*R^4/N^5)^k = (T/N^5)^k*R^(4*k) := by
    rw [show T*R^4/N^5 = (T/N^5)*R^4 by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast R 4,← Real.rpow_mul hR.le]
    norm_num
  change N^11*(T*R^4/N^5)^k*N^l = N^12/R
  apply (eq_div_iff hR.ne').mpr
  calc
    _ = N^11*((T/N^5)^k*N^l)*(R^(4*k)*R) := by rw [hpow]; ring
    _ = N^11*(((T/N^5)^k*N^l)*R^(1+4*k)) := by
      rw [show R^(1+4*k) = R*R^(4*k) by rw [Real.rpow_add hR,Real.rpow_one]]
      ring
    _ = N^12 := by rw [hbal]; ring

end TaoTrudgianYang2025
