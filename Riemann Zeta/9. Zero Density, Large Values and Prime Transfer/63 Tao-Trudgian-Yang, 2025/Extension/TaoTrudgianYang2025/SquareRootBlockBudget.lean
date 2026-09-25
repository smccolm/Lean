import TaoTrudgianYang2025.ContinuousPhaseAbel
import TaoTrudgianYang2025.ThirteenthRootScales

/-! Ordinary third-derivative and Abel budgets at the square-root block scale. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_square_root_block_budget {N μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hmax : N ≤ μ^(-(1:ℝ)/2)) :
    N*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6) ≤ 2*μ^(-(5:ℝ)/12) := by
  have hfirst : N*μ^((1:ℝ)/6) ≤ μ^(-(5:ℝ)/12) := by
    calc
      _ ≤ μ^(-(1:ℝ)/2)*μ^((1:ℝ)/6) :=
        mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg hμ.le _)
      _ = μ^(-(1:ℝ)/3) := by rw [← Real.rpow_add hμ]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hμ hμ1 (by norm_num)
  have hsqrt : Real.sqrt N ≤ μ^(-(1:ℝ)/4) := by
    calc
      _ ≤ Real.sqrt (μ^(-(1:ℝ)/2)) := Real.sqrt_le_sqrt hmax
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hμ.le]; congr 1; ring
  have hsecond : Real.sqrt N*μ^(-(1:ℝ)/6) ≤ μ^(-(5:ℝ)/12) := by
    calc
      _ ≤ μ^(-(1:ℝ)/4)*μ^(-(1:ℝ)/6) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hμ.le _)
      _ = _ := by rw [← Real.rpow_add hμ]; congr 1; ring
  linarith

theorem abel_square_root_block_variation {N K D μ : ℝ}
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hμ : 0 < μ)
    (hmax : N ≤ μ^(-(1:ℝ)/2)) (hslow : K ≤ D*Real.sqrt μ) :
    K*N ≤ D := by
  calc
    _ ≤ (D*Real.sqrt μ)*μ^(-(1:ℝ)/2) := mul_le_mul hslow hmax hN (by positivity)
    _ = D := by
      rw [mul_assoc,Real.sqrt_eq_rpow,← Real.rpow_add hμ]
      norm_num

theorem third_derivative_abel_block_budget {N C K D μ : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hmax : N ≤ μ^(-(1:ℝ)/2)) (hslow : K ≤ D*Real.sqrt μ) :
    (1+2*Real.pi*K*N)*(20*C*(N*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6))) ≤
      40*C*(1+2*Real.pi*D)*μ^(-(5:ℝ)/12) := by
  have hv := abel_square_root_block_variation hN hD hμ hmax hslow
  have hb := third_derivative_square_root_block_budget hμ hμ1 hmax
  have hfactor : 1+2*Real.pi*K*N ≤ 1+2*Real.pi*D := by
    nlinarith [Real.pi_pos]
  have hm := mul_le_mul hfactor
    (mul_le_mul_of_nonneg_left hb (show 0 ≤ 20*C by positivity))
    (show 0 ≤ 20*C*(N*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6)) by positivity)
    (show 0 ≤ 1+2*Real.pi*D by positivity)
  convert hm using 1; ring

theorem square_root_block_floor {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    0 < ⌊μ^(-(1:ℝ)/2)⌋₊ ∧
      μ^(-(1:ℝ)/2)/2 ≤ (⌊μ^(-(1:ℝ)/2)⌋₊:ℝ) ∧
      (⌊μ^(-(1:ℝ)/2)⌋₊:ℝ) ≤ μ^(-(1:ℝ)/2) := by
  apply positive_floor_half_bounds
  have he := Real.rpow_le_rpow_of_exponent_ge hμ hμ1
    (show -(1:ℝ)/2 ≤ 0 by norm_num)
  simpa only [Real.rpow_zero] using he

end TaoTrudgianYang2025
