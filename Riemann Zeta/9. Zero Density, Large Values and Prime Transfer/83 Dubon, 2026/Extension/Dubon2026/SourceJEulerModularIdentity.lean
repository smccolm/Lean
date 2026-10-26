import Dubon2026.SourceModularQDerivativeExpansion
import Dubon2026.SourceAnalyticJDerivativeIdentity
import Dubon2026.SourceJModularQuotient

/-! DUB-17/18 -> Gamma1 regular differential/cusp comparison -> finite-coordinate
integrality. Connect analytic normalized differentiation to the literal
original j Laurent series. The already proved level-one derivative form and
j*Delta identity avoid a separate formal Ramanujan system. -/
namespace Dubon2026.SourceFunctionField.ModularQDerivative
noncomputable section
open UpperHalfPlane ModularForm Derivative SourceDifferential
open scoped MatrixGroups Derivative Manifold

private theorem analytic_derivative_cusp (f : ModularForm 𝒮ℒ 12) :
    AnalyticAt ℂ (cuspFunction 1 (D (f : ℍ → ℂ))) 0 :=
  analyticAt_cuspFunction_zero one_pos
    (periodic_normalizedDerivOfComplex f
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL))
    (normalizedDerivOfComplex_mdifferentiable f.holo')
    (JMultiplicity.isBoundedAtImInfty_D f.holo' (ModularFormClass.bdd_at_infty f))

theorem qExpansion_derivative_bracket (f g : ModularForm 𝒮ℒ 12) :
    (qExpansion 1 (D (f : ℍ → ℂ) * (g : ℍ → ℂ) -
        (f : ℍ → ℂ) * D (g : ℍ → ℂ)) : LaurentSeries ℂ) =
      qEuler ℂ (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) *
        (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) -
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) *
        qEuler ℂ (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL
  have hg := ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods_SL
  have hdf := analytic_derivative_cusp f
  have hdg := analytic_derivative_cusp g
  have h₁ : AnalyticAt ℂ (cuspFunction 1 (D (f : ℍ → ℂ) * (g : ℍ → ℂ))) 0 := by
    rw [cuspFunction_mul hdf.continuousAt hg.continuousAt]
    exact hdf.mul hg
  have h₂ : AnalyticAt ℂ (cuspFunction 1 ((f : ℍ → ℂ) * D (g : ℍ → ℂ))) 0 := by
    rw [cuspFunction_mul hf.continuousAt hdg.continuousAt]
    exact hf.mul hdg
  rw [UpperHalfPlane.qExpansion_sub h₁ h₂, UpperHalfPlane.qExpansion_mul hdf hg,
    UpperHalfPlane.qExpansion_mul hf hdg, PowerSeries.coe_sub,
    PowerSeries.coe_mul, PowerSeries.coe_mul]
  rw [coe_qExpansion_normalizedDerivOfComplex f
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
      f.holo' (ModularFormClass.bdd_at_infty f),
    coe_qExpansion_normalizedDerivOfComplex g
      (SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods_SL)
      g.holo' (ModularFormClass.bdd_at_infty g)]

theorem qEuler_jqModC_mul_discriminant :
    qEuler ℂ (jqModC ℂ) * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) =
      (qExpansion 1 (JMultiplicity.g14 : ℍ → ℂ) : LaurentSeries ℂ) := by
  let f : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let g : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hf : (f : ℍ → ℂ) = (E₄ : ℍ → ℂ) ^ 3 := rfl
  have hg : (g : ℍ → ℂ) = ModularForm.discriminant := rfl
  have hfun : (JMultiplicity.g14.mul g : ℍ → ℂ) =
      D (f : ℍ → ℂ) * (g : ℍ → ℂ) - (f : ℍ → ℂ) * D (g : ℍ → ℂ) := by
    rw [hf, hg, ← JMultiplicity.D_jf_mul_Δ_sq]
    funext z
    change JMultiplicity.g14 z * ModularForm.discriminant z =
      D JMultiplicity.jf z * ModularForm.discriminant z ^ 2
    rw [JMultiplicity.g14_apply]
    ring
  have he := qExpansion_derivative_bracket f g
  rw [← hfun, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_mul, hf, hg] at he
  have he4 : (qExpansion 1 ((E₄ : ℍ → ℂ) ^ 3) : LaurentSeries ℂ) =
      (qExpansion 1 (E₄ : ℍ → ℂ) : LaurentSeries ℂ) ^ 3 := by
    change (qExpansion 1 ((E₄.pow 3) : ℍ → ℂ) : LaurentSeries ℂ) = _
    rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, PowerSeries.coe_pow]
  rw [he4, ← jqModC_mul_discriminant_expansion] at he
  apply mul_right_cancel₀ discriminant_expansion_ne_zero
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at he
  linear_combination -he

end
end Dubon2026.SourceFunctionField.ModularQDerivative
