import Dubon2026.SourceOriginalInverseJAnalyticBound
import Dubon2026.SourceOriginalHolomorphicDifferentials

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay.
The actual derivative identity turns the bounded inverse-j expression into
a positive power of the analytic differential, with a factor of Delta.
Only E4 is divided out, and it tends to one at infinity.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped Topology BigOperators MatrixGroups ModularForm

theorem derivative_power_algebra (M : ℕ) (u a b δ c : ℂ) (ha : a ≠ 0) (hδ : δ ≠ 0) :
    (u * (c * a ^ 2 * b / δ)) ^ (2 * M) =
      c ^ (2 * M) * (u ^ (2 * M) * (a ^ 3 / δ) ^ (M + 1) * (b ^ 2 / δ) ^ M) *
        δ * a ^ (4 * M) / a ^ (3 * (M + 1)) := by
  simp only [mul_pow, div_pow, pow_add, pow_one, pow_mul]
  field_simp
  ring

theorem exists_raw_j_derivative_formula :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ τ : ℍ,
      deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) =
        c * E₄ τ ^ 2 * E₆ τ / ModularForm.discriminant τ := by
  obtain ⟨c, hc, he⟩ := JMultiplicity.exists_D_jf_mul_Δ_eq
  refine ⟨(2 * Real.pi * Complex.I) * c, mul_ne_zero ?_ hc, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  intro τ
  rw [JMultiplicity.deriv_jf_eq _ τ.im_pos, ofComplex_apply]
  apply (eq_div_iff (discriminant_ne_zero τ)).mpr
  calc
    _ = (2 * Real.pi * Complex.I) *
        (Derivative.normalizedDerivOfComplex JMultiplicity.jf τ * ModularForm.discriminant τ) := by ring
    _ = _ := by rw [he]; ring

theorem jf_sub_1728 (τ : ℍ) :
    JMultiplicity.jf τ - 1728 = E₆ τ ^ 2 / ModularForm.discriminant τ := by
  unfold JMultiplicity.jf
  have he := discriminant_eq_E₄_cube_sub_E₆_sq τ
  field_simp [discriminant_ne_zero τ]
  linear_combination -1728 * he

theorem raw_j_derivative_power (c : ℂ)
    (hc : ∀ τ : ℍ, deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) =
      c * E₄ τ ^ 2 * E₆ τ / ModularForm.discriminant τ)
    (M : ℕ) (u : ℂ) (τ : ℍ) (h4 : E₄ τ ≠ 0) :
    (u * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) ^ (2 * M) =
      c ^ (2 * M) * inverseJExpression M u (JMultiplicity.jf τ) *
        ModularForm.discriminant τ * E₄ τ ^ (4 * M) / E₄ τ ^ (3 * (M + 1)) := by
  rw [hc]
  simp only [inverseJExpression]
  rw [jf_sub_1728]
  simpa only [JMultiplicity.jf] using
    derivative_power_algebra M u (E₄ τ) (E₆ τ) (ModularForm.discriminant τ) c h4
      (discriminant_ne_zero τ)

end
end Dubon2026.SourceFunctionField
