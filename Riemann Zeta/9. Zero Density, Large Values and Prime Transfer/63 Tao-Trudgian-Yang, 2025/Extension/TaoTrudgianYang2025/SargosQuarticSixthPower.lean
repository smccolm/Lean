import TaoTrudgianYang2025.SargosQuarticCoverMoment

/-! Sixth powers of the actual source reduction with a harmless integrated error bound. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargos_quarterPower_sixth_le_cube {N : ℝ} (hN : 1 ≤ N) :
    (N^((1:ℝ)/4))^6 ≤ N^3 := by
  have hN0 : 0 ≤ N := by linarith
  have hs := Real.sq_sqrt hN0
  have hs0 := Real.sqrt_nonneg N
  have hsle : Real.sqrt N ≤ N := by
    have hNN : 0 ≤ N*(N-1) := mul_nonneg hN0 (by linarith only [hN])
    nlinarith only [hs,hs0,hN,hNN]
  calc
    _ = ((N^((1:ℝ)/4))^2)^3 := by ring
    _ = (Real.sqrt N)^3 := by rw [sargos_quarterPower_sq hN0]
    _ ≤ _ := pow_le_pow_left₀ hs0 hsle 3

theorem sargos_inverse_sqrt_sixth {Δ : ℝ} (hΔ : 0 < Δ) :
    (1/Real.sqrt Δ)^6 = 1/Δ^3 := by
  rw [div_pow,one_pow]
  have he : (Real.sqrt Δ)^6 = Δ^3 := by
    calc
      _ = ((Real.sqrt Δ)^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hΔ.le]
  rw [he]

theorem sargos_sixth_of_two_blocks {S A B C Δ N : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΔ : 0 < Δ) (hN : 1 ≤ N)
    (hsource : S ≤ C*((1/Real.sqrt Δ)*(A+B)+N^((1:ℝ)/4))) :
    S^6 ≤ 1024*C^6*((1/Δ^3)*(A^6+B^6)+N^3) := by
  have hq : 0 ≤ N^((1:ℝ)/4) := Real.rpow_nonneg (by linarith) _
  have hs : 0 ≤ 1/Real.sqrt Δ := by positivity
  have hp := add_pow_le (mul_nonneg hs (add_nonneg hA hB)) hq 6
  have hab := add_pow_le hA hB 6
  norm_num only [Nat.reduceSub,Nat.reducePow] at hp hab
  rw [mul_pow,sargos_inverse_sqrt_sixth hΔ] at hp
  have hq6 := sargos_quarterPower_sixth_le_cube hN
  have hinside : ((1/Real.sqrt Δ)*(A+B)+N^((1:ℝ)/4))^6 ≤
      1024*((1/Δ^3)*(A^6+B^6)+N^3) := by
    have hm := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 1/Δ^3)
    have hN3 : 0 ≤ N^3 := by positivity
    nlinarith only [hp,hm,hq6,hN3]
  calc
    _ ≤ (C*((1/Real.sqrt Δ)*(A+B)+N^((1:ℝ)/4)))^6 :=
      pow_le_pow_left₀ hS hsource 6
    _ = C^6*((1/Real.sqrt Δ)*(A+B)+N^((1:ℝ)/4))^6 := mul_pow _ _ _
    _ ≤ C^6*(1024*((1/Δ^3)*(A^6+B^6)+N^3)) :=
      mul_le_mul_of_nonneg_left hinside (pow_nonneg hC 6)
    _ = _ := by ring

end TaoTrudgianYang2025
