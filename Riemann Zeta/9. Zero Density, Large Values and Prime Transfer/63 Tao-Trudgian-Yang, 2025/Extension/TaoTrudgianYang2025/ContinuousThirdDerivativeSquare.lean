import TaoTrudgianYang2025.ContinuousThirdDerivativeWeyl
import TaoTrudgianYang2025.ThirdDerivativeWeylScale
import TaoTrudgianYang2025.ThirdDerivativeRootScale
import TaoTrudgianYang2025.ThirdDerivativeFloor

/-! All-length third-derivative estimate at the physical cube-root scale. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem continuous_third_derivative_square_bound
    (F F' F'' F''' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ R : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hR : 1 ≤ R) (hscale : R^3*μ = 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x ∈ Icc A (A+N), HasDerivAt F'' (F''' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), μ ≤ F''' x)
    (hhi : ∀ x ∈ Icc A (A+N), F''' x ≤ C*μ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖^2 ≤
      52*C*(N:ℝ)^2/R+384*N*R := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  by_cases hRN : R ≤ N
  · obtain ⟨hpos,hHN,hlow,hupper,hHμ⟩ :=
      third_derivative_floor_shift N hR hRN hμ hscale
    have hb := continuous_third_derivative_weyl F F' F'' F''' A N ⌊R⌋₊
      (zero_le_one.trans hC) hμ hHμ hF hF' hF'' hlo hhi
    have hn := third_derivative_weyl_normalize (H := (⌊R⌋₊:ℝ)) (Nat.cast_nonneg N)
      (by exact_mod_cast hpos) (by exact_mod_cast hHN) (zero_le_one.trans hC) hμ
      (by simpa only [Nat.cast_add] using hb)
    exact third_derivative_optimized_square_scale (Nat.cast_nonneg N) hRp hC hμ
      hlow hupper hscale hn
  · have hNR : (N:ℝ) ≤ R := (lt_of_not_ge hRN).le
    have htriv :
        ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤ N := by
      calc
        _ ≤ ∑ n ∈ Finset.range N, ‖fordAdditiveCharacter (F (A+n))‖ :=
          norm_sum_le _ _
        _ = N := by simp [fordAdditiveCharacter,Complex.norm_exp]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htriv 2
    have hNRmul := mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg (α := ℝ) N)
    have hpositive : 0 ≤ 52*C*(N:ℝ)^2/R := by positivity
    have hN : 0 ≤ (N:ℝ)*R := by positivity
    nlinarith

end TaoTrudgianYang2025
