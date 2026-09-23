import TaoTrudgianYang2025.SargosQuarticSexticFreeze

/-! Uniform coefficient control on a genuine unit-width parameter rectangle. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticSextic_coefficient_bound {x c y d R B η : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hxR : 1/x ≤ R) (hcR : 1/c ≤ R)
    (hxc : |x-c| ≤ 1) (hy : |y| ≤ B) (hd : |d| ≤ B) (hyd : |y-d| ≤ η) :
    |y^2/x-d^2/c| ≤ 2*η*B*R+B^2*R^2 := by
  have hR : 0 ≤ R := (by positivity : 0 ≤ 1/x).trans hxR
  have hB : 0 ≤ B := (abs_nonneg d).trans hd
  have hη : 0 ≤ η := (abs_nonneg (y-d)).trans hyd
  have hinv : |1/x-1/c| ≤ R^2 := by
    have he : 1/x-1/c = (c-x)*(1/x)*(1/c) := by field_simp
    rw [he,abs_mul,abs_mul,abs_sub_comm c x,
      abs_of_pos (by positivity : 0 < 1/x),abs_of_pos (by positivity : 0 < 1/c)]
    calc
      _ ≤ 1*R*R := mul_le_mul
        (mul_le_mul hxc hxR (by positivity) (by norm_num)) hcR (by positivity) (by positivity)
      _ = _ := by ring
  have hadd : |y+d| ≤ 2*B := (abs_add_le y d).trans (by linarith only [hy,hd])
  have hd2 : d^2 ≤ B^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  calc
    _ = |(y-d)*(y+d)*(1/x)+d^2*(1/x-1/c)| := by congr 1; ring
    _ ≤ |(y-d)*(y+d)*(1/x)|+|d^2*(1/x-1/c)| := abs_add_le _ _
    _ = |y-d| * |y+d| * (1/x)+d^2*|1/x-1/c| := by
      rw [abs_mul,abs_mul,abs_mul,abs_sq,abs_of_pos (by positivity : 0 < 1/x)]
    _ ≤ η*(2*B)*R+B^2*R^2 := add_le_add
      (mul_le_mul (mul_le_mul hyd hadd (abs_nonneg _) hη) hxR
        (by positivity) (by positivity))
      (mul_le_mul hd2 hinv (abs_nonneg _) (sq_nonneg _))
    _ = _ := by ring

theorem sargosQuarticSextic_rectangle_coefficient {Δ M c d x y : ℝ}
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2) (hM : 0 < M)
    (hc : 1/(8*Δ) ≤ c) (hd : |d| ≤ 5/(Δ*M^3))
    (hx : x ∈ Icc c (c+1)) (hy : y ∈ Icc d (d+2/M^3)) :
    |y^2/x-d^2/c| ≤ 2496/M^6 := by
  have hcp : 0 < c := (by positivity : 0 < 1/(8*Δ)).trans_le hc
  have hxp : 0 < x := hcp.trans_le hx.1
  have hinvc : 1/c ≤ 8*Δ := by
    apply (div_le_iff₀ hcp).2
    have hh := (div_le_iff₀ (by positivity : 0 < 8*Δ)).mp hc
    nlinarith only [hh]
  have hinvx : 1/x ≤ 8*Δ := (one_div_le_one_div_of_le hcp hx.1).trans hinvc
  have hxc : |x-c| ≤ 1 := by rw [abs_of_nonneg (by linarith only [hx.1])]; linarith only [hx.2]
  have hyd : |y-d| ≤ 2/M^3 := by
    rw [abs_of_nonneg (by linarith only [hy.1])]
    linarith only [hy.2]
  have hheight : 5/(Δ*M^3)+2/M^3 ≤ 6/(Δ*M^3) := by
    calc
      _ = (5+2*Δ)/(Δ*M^3) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hΔ₁]) (by positivity)
  have hyB : |y| ≤ 6/(Δ*M^3) := by
    have hh : |y| ≤ |d|+|y-d| := by
      simpa only [show d+(y-d) = y by ring] using abs_add_le d (y-d)
    exact hh.trans ((add_le_add hd hyd).trans hheight)
  have hdB : |d| ≤ 6/(Δ*M^3) :=
    hd.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have hh := sargosQuarticSextic_coefficient_bound hxp hcp hinvx hinvc hxc hyB hdB hyd
  calc
    _ ≤ 2*(2/M^3)*(6/(Δ*M^3))*(8*Δ)+(6/(Δ*M^3))^2*(8*Δ)^2 := hh
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
