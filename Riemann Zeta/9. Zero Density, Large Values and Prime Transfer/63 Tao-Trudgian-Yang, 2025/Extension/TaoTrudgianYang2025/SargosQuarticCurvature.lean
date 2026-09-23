import TaoTrudgianYang2025.SargosSlowAbel
import GuthMaynard.SecondDerivative

/-! Exact quartic second differences and a verified large-alpha curvature cutoff. -/

noncomputable section

open GafniTao Set RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem sargos_quartic_second_difference (x α γ : ℝ) :
    (((x+2)^2*α+(x+2)^4*γ)-((x+1)^2*α+(x+1)^4*γ))-
      (((x+1)^2*α+(x+1)^4*γ)-(x^2*α+x^4*γ)) =
        2*α+(12*x^2+24*x+14)*γ := by ring

theorem sargos_quartic_difference_coefficient {N x : ℝ}
    (hN : 1 ≤ N) (hx : x ∈ Icc N (2*N)) :
    0 ≤ 12*x^2+24*x+14 ∧ 12*x^2+24*x+14 ≤ 110*N^2 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxsq : x^2 ≤ (2*N)^2 := pow_le_pow_left₀ hx0 hx.2 2
  constructor
  · positivity
  · nlinarith [sq_nonneg (N-1)]

theorem sargos_quartic_difference_error {N x γ : ℝ}
    (hN : 1 ≤ N) (hx : x ∈ Icc N (2*N)) (hγ : |γ| ≤ 1/N^3) :
    |(12*x^2+24*x+14)*γ| ≤ 110/N := by
  have hNp : 0 < N := by linarith
  obtain ⟨hp,hP⟩ := sargos_quartic_difference_coefficient hN hx
  rw [abs_mul,abs_of_nonneg hp]
  calc
    _ ≤ (110*N^2)*(1/N^3) := mul_le_mul hP hγ (abs_nonneg γ) (by positivity)
    _ = _ := by field_simp

theorem sargos_quartic_curvature {N x α γ : ℝ}
    (hN : 1 ≤ N) (hx : x ∈ Icc N (2*N)) (hγ : |γ| ≤ 1/N^3)
    (hα : 128/N ≤ α) :
    α ≤ 2*α+(12*x^2+24*x+14)*γ ∧
      2*α+(12*x^2+24*x+14)*γ ≤ 3*α := by
  have hNp : 0 < N := by linarith
  have he := abs_le.mp (sargos_quartic_difference_error hN hx hγ)
  have h110 : 110/N ≤ α := (div_le_div_of_nonneg_right (by norm_num) hNp.le).trans hα
  constructor <;> linarith [he.1,he.2]

end TaoTrudgianYang2025
