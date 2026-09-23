import TaoTrudgianYang2025.SargosFiniteCoverIntegral

/-! The actual transformed source rectangle has the required cover size and corners. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

def sargosQuarticParameterHeight (N Δ : ℝ) : ℝ := 1/(16*Δ^4*N^3)

theorem sargosQuarticParameterHeight_le {N Δ M : ℝ}
    (hN : 0 < N) (hΔ : 0 < Δ) (hM : 0 < M) (hscale : M ≤ 4*Δ*N) :
    sargosQuarticParameterHeight N Δ ≤ 4/(Δ*M^3) := by
  have hp := pow_le_pow_left₀ hM.le hscale 3
  have hh := mul_le_mul_of_nonneg_left hp hΔ.le
  unfold sargosQuarticParameterHeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hh]

theorem sargosQuarticHorizontalGrid_count {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2) :
    (sargosIntervalGridCount (1/(8*Δ)) 1 : ℝ) ≤ 2/Δ := by
  have hh := sargosIntervalGridCount_le (by positivity : 0 ≤ 1/(8*Δ))
    (by norm_num : (0:ℝ) < 1)
  apply hh.trans
  rw [div_one]
  apply (le_div_iff₀ hΔ).2
  have he : (1/(8*Δ)+2)*Δ = 1/8+2*Δ := by field_simp
  rw [he]
  linarith only [hΔ₁]

theorem sargosQuarticVerticalGrid_count {N Δ M : ℝ}
    (hN : 0 < N) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2) (hM : 0 < M)
    (hscale : M ≤ 4*Δ*N) :
    (sargosIntervalGridCount (2*sargosQuarticParameterHeight N Δ) (2/M^3) : ℝ) ≤ 5/Δ := by
  have hY : 0 ≤ sargosQuarticParameterHeight N Δ := by
    unfold sargosQuarticParameterHeight
    positivity
  have hh := sargosIntervalGridCount_le (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hY)
    (by positivity : 0 < 2/M^3)
  have he : (2*sargosQuarticParameterHeight N Δ)/(2/M^3) =
      sargosQuarticParameterHeight N Δ*M^3 := by field_simp
  rw [he] at hh
  have hheight := sargosQuarticParameterHeight_le hN hΔ hM hscale
  have hm := mul_le_mul_of_nonneg_right hheight (by positivity : 0 ≤ M^3)
  have he' : (4/(Δ*M^3))*M^3 = 4/Δ := by field_simp
  rw [he'] at hm
  apply hh.trans
  apply (le_div_iff₀ hΔ).2
  have hm' := (le_div_iff₀ hΔ).mp hm
  nlinarith only [hm',hΔ₁]

theorem sargosQuarticVerticalGrid_corner {N Δ M : ℝ}
    (hN : 0 < N) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2) (hM : 0 < M)
    (hscale : M ≤ 4*Δ*N) {j : ℕ}
    (hj : j ∈ Finset.range
      (sargosIntervalGridCount (2*sargosQuarticParameterHeight N Δ) (2/M^3))) :
    |-sargosQuarticParameterHeight N Δ+(j:ℝ)*(2/M^3)| ≤ 5/(Δ*M^3) := by
  have hY : 0 ≤ sargosQuarticParameterHeight N Δ := by
    unfold sargosQuarticParameterHeight
    positivity
  have hb := sargosIntervalGrid_corner_bounds (a := -sargosQuarticParameterHeight N Δ)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hY) (by positivity : 0 < 2/M^3) hj
  have hheight := sargosQuarticParameterHeight_le hN hΔ hM hscale
  have htop : 4/(Δ*M^3)+2/M^3 ≤ 5/(Δ*M^3) := by
    calc
      _ = (4+2*Δ)/(Δ*M^3) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hΔ₁]) (by positivity)
  have hyupper : sargosQuarticParameterHeight N Δ+2/M^3 ≤ 5/(Δ*M^3) :=
    (add_le_add hheight le_rfl).trans htop
  apply abs_le.mpr
  constructor <;> linarith only [hb.1,hb.2,hyupper,show (0:ℝ) ≤ 2/M^3 by positivity]

end TaoTrudgianYang2025
