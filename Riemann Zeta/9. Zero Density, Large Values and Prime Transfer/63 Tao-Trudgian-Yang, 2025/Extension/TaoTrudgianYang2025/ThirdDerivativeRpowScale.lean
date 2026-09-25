import TaoTrudgianYang2025.SecondDerivativeScale

/-! Exact physical sixth- and cube-root scales for the third-derivative test. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_rpow_scale {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    1 ≤ μ^(-(1:ℝ)/3) ∧
      (μ^(-(1:ℝ)/3))^3*μ = 1 ∧
      Real.sqrt (μ^(-(1:ℝ)/3)) = μ^(-(1:ℝ)/6) ∧
      1/Real.sqrt (μ^(-(1:ℝ)/3)) = μ^((1:ℝ)/6) := by
  have hR := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hμ hμ1
    (show -(1:ℝ)/3 ≤ 0 by norm_num)
  have hcube : (μ^(-(1:ℝ)/3))^3*μ = 1 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hμ.le]
    norm_num
    rw [Real.rpow_neg_one,inv_mul_cancel₀ hμ.ne']
  have hs : Real.sqrt (μ^(-(1:ℝ)/3)) = μ^(-(1:ℝ)/6) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hμ.le]
    congr 1
    norm_num
  refine ⟨hR,hcube,hs,?_⟩
  rw [hs,show -(1:ℝ)/6 = -((1:ℝ)/6) by ring,Real.rpow_neg hμ.le]
  simp

end TaoTrudgianYang2025
