import TaoTrudgianYang2025.SecondDerivativeScale

/-! Root-scale inequalities for the optimized third-derivative shift. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_root_scale {R H μ : ℝ}
    (hR : 0 < R) (hμ : 0 < μ) (hlo : R/2 ≤ H) (hhi : H ≤ R)
    (hscale : R^3*μ = 1) :
    Real.sqrt μ*Real.sqrt H ≤ 1/R ∧
      1/(Real.sqrt H*Real.sqrt μ) ≤ 2*R := by
  have hH : 0 < H := lt_of_lt_of_le (by positivity) hlo
  let a := Real.sqrt μ*Real.sqrt H
  have ha : 0 < a := mul_pos (Real.sqrt_pos.mpr hμ) (Real.sqrt_pos.mpr hH)
  have ha2 : a^2 = μ*H := by
    dsimp [a]
    rw [mul_pow,Real.sq_sqrt hμ.le,Real.sq_sqrt hH.le]
  have hu : (a*R)^2 ≤ 1 := by
    rw [mul_pow,ha2]
    calc
      μ*H*R^2 ≤ μ*R*R^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hμ.le) (sq_nonneg R)
      _ = 1 := by nlinarith [hscale]
  have hl : 2 ≤ (2*R*a)^2 := by
    have hb := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 4*μ*R^2 by positivity)
    calc
      2 = (R/2)*(4*μ*R^2) := by nlinarith [hscale]
      _ ≤ H*(4*μ*R^2) := hb
      _ = (2*R*a)^2 := by rw [mul_pow,mul_pow,ha2]; ring
  have hau : a*R ≤ 1 := by nlinarith
  have hal : 1 ≤ 2*R*a := by nlinarith [mul_pos (by positivity : 0 < 2*R) ha]
  constructor
  · exact (le_div_iff₀ hR).mpr hau
  · rw [mul_comm (Real.sqrt H)]
    exact (div_le_iff₀ ha).mpr hal

theorem third_derivative_optimized_square_scale {S N H R C μ : ℝ}
    (hN : 0 ≤ N) (hR : 0 < R) (hC : 1 ≤ C) (hμ : 0 < μ)
    (hlo : R/2 ≤ H) (hhi : H ≤ R) (hscale : R^3*μ = 1)
    (hb : S^2 ≤ 2*N^2/H+48*C*N^2*Real.sqrt μ*Real.sqrt H+
      192*N/(Real.sqrt H*Real.sqrt μ)) :
    S^2 ≤ 52*C*N^2/R+384*N*R := by
  have hH : 0 < H := lt_of_lt_of_le (by positivity) hlo
  have hs := third_derivative_root_scale hR hμ hlo hhi hscale
  have hfirst : 2*N^2/H ≤ 4*N^2/R := by
    apply (div_le_div_iff₀ hH hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg N)]
  have hsecond := mul_le_mul_of_nonneg_left hs.1
    (show 0 ≤ 48*C*N^2 by positivity)
  have hthird := mul_le_mul_of_nonneg_left hs.2
    (show 0 ≤ 192*N by positivity)
  have hCfirst := mul_le_mul_of_nonneg_right hC
    (show 0 ≤ 4*N^2/R by positivity)
  calc
    S^2 ≤ 4*N^2/R+48*C*N^2/R+384*N*R := by
      simp only [div_eq_mul_inv] at hb hfirst hsecond hthird ⊢
      nlinarith
    _ ≤ 52*C*N^2/R+384*N*R := by
      simp only [div_eq_mul_inv] at hCfirst ⊢
      nlinarith

end TaoTrudgianYang2025
