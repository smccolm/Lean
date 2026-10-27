import Dubon2026.SourceGammaOneRegularCuspForms
import Dubon2026.SourceJEulerModularIdentity

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> exact
Fourier normalization. Clear the existing modular denominator and Delta.
The proved q-Euler identity for j then identifies the actual cusp expansion
with x times q d(j)/dq. The analytic factor 2*pi*i is removed explicitly. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane ModularForm SourceDifferential
open scoped MatrixGroups ModularForm
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

theorem normalized_cusp_qExpansion (hT : ModularGroup.T ∈ Γ)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (x : LaurentSeries ℂ) (hr : x * ModularRatios.qL h = ModularRatios.qL g)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
    (he : ∀ τ : ℍ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) :
    (qExpansion 1 ((2 * Real.pi * Complex.I)⁻¹ • F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) :
      LaurentSeries ℂ) = x * qEuler ℂ (jqModC ℂ) := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let F₀ : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 := c⁻¹ • F
  let d : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ Γ)
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  let j : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 14 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ Γ) JMultiplicity.g14
  have hm : (((F₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2).mul h).mul d).mcast
      (show 2 + k + 12 = k + 14 by omega) = g.mul j := by
    ext τ
    change (c⁻¹ * F τ * h τ) * ModularForm.discriminant τ = g τ * JMultiplicity.g14 τ
    rw [mul_assoc c⁻¹ (F τ) (h τ), he, JMultiplicity.deriv_jf_eq _ τ.im_pos,
      ofComplex_apply, JMultiplicity.g14_apply]
    change (c⁻¹ * (g τ * (c * Derivative.normalizedDerivOfComplex JMultiplicity.jf τ))) *
      ModularForm.discriminant τ =
        g τ * (Derivative.normalizedDerivOfComplex JMultiplicity.jf τ * ModularForm.discriminant τ)
    field_simp
  have hq := congrArg (ModularRatios.qL (Γ := Γ)) hm
  simp only [ModularRatios.qL, ModularForm.qExpansion_mcast] at hq
  change ModularRatios.qL (((F₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2).mul h).mul d) =
    ModularRatios.qL (g.mul j) at hq
  rw [ModularRatios.qL_mul hT, ModularRatios.qL_mul hT, ModularRatios.qL_mul hT] at hq
  have hj : ModularRatios.qL j = qEuler ℂ (jqModC ℂ) * ModularRatios.qL d :=
    ModularQDerivative.qEuler_jqModC_mul_discriminant.symm
  rw [hj, ← hr] at hq
  apply mul_right_cancel₀ (mul_ne_zero (ModularRatios.qL_ne_zero hT h hh)
    (show ModularRatios.qL d ≠ 0 from discriminant_expansion_ne_zero))
  change ModularRatios.qL (F₀ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) *
    (ModularRatios.qL h * ModularRatios.qL d) = _
  linear_combination hq

end
end Dubon2026.SourceFunctionField.GammaOne
