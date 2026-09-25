import TaoTrudgianYang2025.SecondDerivativeScale

/-! Passing from the optimized squared bound to a conventional norm estimate. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_norm_of_square {S N R C : ℝ}
    (hN : 0 ≤ N) (hR : 0 < R) (hC : 1 ≤ C)
    (hb : S^2 ≤ 52*C*N^2/R+384*N*R) :
    S ≤ 20*C*(N/Real.sqrt R+Real.sqrt N*Real.sqrt R) := by
  let u := N/Real.sqrt R
  let v := Real.sqrt N*Real.sqrt R
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu2 : u^2 = N^2/R := by
    dsimp [u]
    rw [div_pow,Real.sq_sqrt hR.le]
  have hv2 : v^2 = N*R := by
    dsimp [v]
    rw [mul_pow,Real.sq_sqrt hN,Real.sq_sqrt hR.le]
  have hcu : 52*C ≤ 400*C^2 := by nlinarith
  have hcv : (384:ℝ) ≤ 400*C^2 := by nlinarith
  have hbu := mul_le_mul_of_nonneg_right hcu (sq_nonneg u)
  have hbv := mul_le_mul_of_nonneg_right hcv (sq_nonneg v)
  have hb' : S^2 ≤ 52*C*u^2+384*v^2 := by
    rw [hu2,hv2]
    simpa only [div_eq_mul_inv,mul_assoc] using hb
  have hsq : S^2 ≤ (20*C*(u+v))^2 := by
    have hcuv := mul_nonneg (sq_nonneg C) (mul_nonneg hu hv)
    nlinarith
  have hnonneg : 0 ≤ 20*C*(u+v) := by positivity
  change S ≤ 20*C*(u+v)
  nlinarith

end TaoTrudgianYang2025
