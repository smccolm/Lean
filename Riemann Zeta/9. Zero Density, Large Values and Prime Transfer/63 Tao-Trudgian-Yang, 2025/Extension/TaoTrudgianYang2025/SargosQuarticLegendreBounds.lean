import TaoTrudgianYang2025.SargosQuarticLegendreRemainder

/-! Explicit uniform bounds for the actual quartic Legendre residual and its derivative. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuartic_remainder_product_bound {α γ x : ℝ}
    (hα : 0 < α) (hx : 0 ≤ x) (hu : |2*γ*x^2/α| ≤ 1/12) :
    |α*x^2*(2*γ*x^2/α)^3*sargosQuarticRemainderPolynomial (2*γ*x^2/α)| ≤
      40*|γ|^3*x^8/α^2 := by
  calc
    _ = α*x^2*(2 * |γ| * x^2/α)^3*
        |sargosQuarticRemainderPolynomial (2*γ*x^2/α)| := by
      rw [abs_mul,abs_mul,abs_mul,abs_pow,abs_pow,abs_div,abs_mul,abs_mul,
        abs_of_pos hα,abs_of_nonneg hx]
      norm_num
    _ ≤ α*x^2*(2 * |γ| * x^2/α)^3*5 :=
      mul_le_mul_of_nonneg_left (sargosQuarticRemainderPolynomial_bound hu) (by positivity)
    _ = _ := by field_simp; ring

theorem sargosQuartic_remainder_derivative_product_bound {α γ x : ℝ}
    (hα : 0 < α) (hx : 0 ≤ x) (hu : |2*γ*x^2/α| ≤ 1/12) :
    |x*(2*γ*x^2/α)^3*sargosQuarticRemainderDerivativePolynomial (2*γ*x^2/α)| ≤
      128*|γ|^3*x^7/α^3 := by
  calc
    _ = x*(2 * |γ| * x^2/α)^3*
        |sargosQuarticRemainderDerivativePolynomial (2*γ*x^2/α)| := by
      rw [abs_mul,abs_mul,abs_pow,abs_div,abs_mul,abs_mul,
        abs_of_nonneg hx,abs_of_pos hα,abs_pow,abs_of_nonneg hx]
      norm_num
    _ ≤ x*(2 * |γ| * x^2/α)^3*16 :=
      mul_le_mul_of_nonneg_left (sargosQuarticRemainderDerivativePolynomial_bound hu)
        (by positivity)
    _ = _ := by field_simp; ring

theorem sargosQuarticLegendreRemainder_bound {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    |sargosQuarticLegendreRemainder N α γ y| ≤ 10240*|γ|^3*N^8/α^2 := by
  have hx := sargosQuarticInverseSlope_mem hN hα hγ hy
  have hxc : sargosQuarticInverseSlope N α γ y ∈ Icc N (2*N) := ⟨hx.1.le,hx.2.le⟩
  rw [sargosQuarticLegendreRemainder_eq (ne_of_gt hα) hy]
  calc
    _ ≤ 40*|γ|^3*(sargosQuarticInverseSlope N α γ y)^8/α^2 :=
      sargosQuartic_remainder_product_bound hα (hN.le.trans hx.1.le)
        (sargosQuartic_ratio_bound hN hα hγ hxc)
    _ ≤ 40*|γ|^3*(2*N)^8/α^2 := by
      gcongr
      exact hN.le.trans hx.1.le
      exact hx.2.le
    _ = _ := by ring

theorem sargosQuarticLegendreRemainderDerivative_bound {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    |sargosQuarticLegendreRemainderDerivative N α γ y| ≤
      16384*|γ|^3*N^7/α^3 := by
  have hx := sargosQuarticInverseSlope_mem hN hα hγ hy
  have hxc : sargosQuarticInverseSlope N α γ y ∈ Icc N (2*N) := ⟨hx.1.le,hx.2.le⟩
  rw [sargosQuarticLegendreRemainderDerivative_eq (ne_of_gt hα) hy]
  calc
    _ ≤ 128*|γ|^3*(sargosQuarticInverseSlope N α γ y)^7/α^3 :=
      sargosQuartic_remainder_derivative_product_bound hα (hN.le.trans hx.1.le)
        (sargosQuartic_ratio_bound hN hα hγ hxc)
    _ ≤ 128*|γ|^3*(2*N)^7/α^3 := by
      gcongr
      exact hN.le.trans hx.1.le
      exact hx.2.le
    _ = _ := by ring

theorem sargosQuarticLegendreRemainder_deriv_bound {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    |deriv (sargosQuarticLegendreRemainder N α γ) y| ≤ 16384*|γ|^3*N^7/α^3 := by
  rw [(sargosQuarticLegendreRemainder_hasDerivAt hN hα hγ hy).deriv]
  exact sargosQuarticLegendreRemainderDerivative_bound hN hα hγ hy

end TaoTrudgianYang2025
