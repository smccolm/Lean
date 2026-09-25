import TaoTrudgianYang2025.ThirteenthRootScales
import TaoTrudgianYang2025.RobertSargosZeroQLeading

/-! The zero-q curvature, slow variation and block length at physical scales. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_curvature_scale {r lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hr : |r| ≤ lam^(-(1:ℝ)/13)) :
    2*|r| *lam ≤ 1 := by
  let T := lam^(-(1:ℝ)/13)
  obtain ⟨hT,hscale⟩ := thirteenth_root_physical_scale hlam hsmall
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have hp : 2 ≤ T^12 := hT.trans (le_self_pow₀ hT1 (by norm_num : 12 ≠ 0))
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ T*lam by positivity)
  have he : T^12*(T*lam) = 1 := by
    calc
      _ = T^13*lam := by ring
      _ = 1 := hscale
  rw [he] at hm
  have hr' : |r| ≤ T := hr
  nlinarith [mul_le_mul_of_nonneg_right hr' hlam.le]

theorem robertSargos_zero_q_slow_scale {h r C lam : ℝ}
    (hC : 0 ≤ C) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hh : 0 ≤ h) (hhr : 0 ≤ h+r)
    (hhmax : h ≤ lam^(-(2:ℝ)/13)) (hhrmax : h+r ≤ lam^(-(2:ℝ)/13))
    (hr : 1 ≤ |r|) :
    C*lam*(h^3+(h+r)^3)/3 ≤ C*Real.sqrt (2*|r| *lam) := by
  have hcube : (lam^(-(2:ℝ)/13))^3 = lam^(-(6:ℝ)/13) := by
    rw [← Real.rpow_mul_natCast hlam.le]
    congr 1
    norm_num
  have hh3 : h^3 ≤ lam^(-(6:ℝ)/13) := (pow_le_pow_left₀ hh hhmax 3).trans_eq hcube
  have hhr3 : (h+r)^3 ≤ lam^(-(6:ℝ)/13) := (pow_le_pow_left₀ hhr hhrmax 3).trans_eq hcube
  have hprod : lam*lam^(-(6:ℝ)/13) = lam^((7:ℝ)/13) := by
    calc
      _ = lam^(1:ℝ)*lam^(-(6:ℝ)/13) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hlam]; congr 1; norm_num
  have hs : lam^((7:ℝ)/13) ≤ Real.sqrt lam := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by norm_num)
  have hmu : lam ≤ 2*|r| *lam := by nlinarith
  have hs2 := Real.sqrt_le_sqrt hmu
  have hm := mul_le_mul_of_nonneg_left (add_le_add hh3 hhr3) (mul_nonneg hC hlam.le)
  have hsC := mul_le_mul_of_nonneg_left hs hC
  have hs2C := mul_le_mul_of_nonneg_left hs2 hC
  have he : C*lam*(lam^(-(6:ℝ)/13)+lam^(-(6:ℝ)/13)) = 2*C*lam^((7:ℝ)/13) := by
    calc
      _ = 2*C*(lam*lam^(-(6:ℝ)/13)) := by ring
      _ = _ := by rw [hprod]
  rw [he] at hm
  nlinarith [mul_nonneg hC (Real.sqrt_nonneg (2*|r| *lam))]

theorem robertSargos_zero_q_block_length {r lam M : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hr : 1 ≤ |r|)
    (hM : lam^(-(8:ℝ)/13) ≤ M) :
    (2*|r| *lam)^(-(1:ℝ)/2) ≤ M := by
  have hmu : lam ≤ 2*|r| *lam := by nlinarith
  exact (Real.rpow_le_rpow_of_nonpos hlam hmu (by norm_num : -(1:ℝ)/2 ≤ 0)).trans
    ((Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by norm_num : -(8:ℝ)/13 ≤ -1/2)).trans hM)

end TaoTrudgianYang2025
