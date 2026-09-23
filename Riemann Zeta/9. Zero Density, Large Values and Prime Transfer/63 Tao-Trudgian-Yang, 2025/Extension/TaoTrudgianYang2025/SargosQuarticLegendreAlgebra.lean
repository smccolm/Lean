import TaoTrudgianYang2025.SargosQuarticPhase

/-! Exact rational algebra and small-parameter bounds for the quartic Legendre remainder. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosQuarticRemainderPolynomial (u : ℝ) : ℝ :=
  3+u*(13+u*((39/2:ℝ)+u*(15+u*(6+u))))

def sargosQuarticRemainderDerivativePolynomial (u : ℝ) : ℝ :=
  12+u*(29+u*(30+u*(15+u*3)))

theorem sargosQuartic_legendre_algebra {α : ℝ} (hα : α ≠ 0) (γ x : ℝ) :
    sargosQuarticPhase α γ x-sargosQuarticSlope α γ x*x+
      (sargosQuarticSlope α γ x)^2/(4*α)-
      γ*(sargosQuarticSlope α γ x)^4/(16*α^4)+
      γ^2*(sargosQuarticSlope α γ x)^6/(16*α^7) =
    α*x^2*(2*γ*x^2/α)^3*sargosQuarticRemainderPolynomial (2*γ*x^2/α) := by
  unfold sargosQuarticPhase sargosQuarticSlope sargosQuarticRemainderPolynomial
  field_simp
  ring

theorem sargosQuartic_legendre_derivative_algebra {α : ℝ} (hα : α ≠ 0) (γ x : ℝ) :
    -x+sargosQuarticSlope α γ x/(2*α)-
      γ*(sargosQuarticSlope α γ x)^3/(4*α^4)+
      3*γ^2*(sargosQuarticSlope α γ x)^5/(8*α^7) =
    x*(2*γ*x^2/α)^3*sargosQuarticRemainderDerivativePolynomial (2*γ*x^2/α) := by
  unfold sargosQuarticSlope sargosQuarticRemainderDerivativePolynomial
  field_simp
  ring

private theorem abs_add_mul_bound {a u v A U V : ℝ}
    (ha : |a| ≤ A) (hu : |u| ≤ U) (hv : |v| ≤ V) :
    |a+u*v| ≤ A+U*V := by
  calc
    _ ≤ |a|+|u*v| := abs_add_le _ _
    _ = |a| + |u| * |v| := by rw [abs_mul]
    _ ≤ _ := add_le_add ha (mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu))

theorem sargosQuarticRemainderPolynomial_bound {u : ℝ} (hu : |u| ≤ 1/12) :
    |sargosQuarticRemainderPolynomial u| ≤ 5 := by
  have h6 : |6+u| ≤ 6+1/12 :=
    (abs_add_le _ _).trans (add_le_add (by norm_num) hu)
  have h15 := abs_add_mul_bound (by norm_num : |(15:ℝ)| ≤ 15) hu h6
  have h39 := abs_add_mul_bound (by norm_num : |(39/2:ℝ)| ≤ 39/2) hu h15
  have h13 := abs_add_mul_bound (by norm_num : |(13:ℝ)| ≤ 13) hu h39
  exact (abs_add_mul_bound (by norm_num : |(3:ℝ)| ≤ 3) hu h13).trans (by norm_num)

theorem sargosQuarticRemainderDerivativePolynomial_bound {u : ℝ} (hu : |u| ≤ 1/12) :
    |sargosQuarticRemainderDerivativePolynomial u| ≤ 16 := by
  have h15 := abs_add_mul_bound (by norm_num : |(15:ℝ)| ≤ 15) hu
    (by norm_num : |(3:ℝ)| ≤ 3)
  have h30 := abs_add_mul_bound (by norm_num : |(30:ℝ)| ≤ 30) hu h15
  have h29 := abs_add_mul_bound (by norm_num : |(29:ℝ)| ≤ 29) hu h30
  exact (abs_add_mul_bound (by norm_num : |(12:ℝ)| ≤ 12) hu h29).trans (by norm_num)

end TaoTrudgianYang2025
