import Dubon2026.SourceGammaOneRealizationAlgebra
import Dubon2026.SourceOriginalAnalyticDerivativeOrder

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> local j
coordinate. The already proved literal j-series identity and nowhere-zero
discriminant identify the actual analytic coordinate at every complex point.
No degree, elliptic stabilizer or global ramification calculation is needed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem realize_jCoordinateOver
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    realize Γ (jCoordinateOver Γ ℂ : LaurentSeries ℂ) τ = JMultiplicity.jf τ := by
  let f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ Γ)
      ((ModularForm.E₄.pow 3).mcast (by norm_num))
  let g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ Γ)
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hg : g τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  have hq : (jCoordinateOver Γ ℂ : LaurentSeries ℂ) * ModularRatios.qL g =
      ModularRatios.qL f := by
    change coeffEmb ℂ jq * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) =
      (qExpansion 1 (((ModularForm.E₄.pow 3).mcast (by norm_num) : ModularForm 𝒮ℒ 12) : ℍ → ℂ) : LaurentSeries ℂ)
    rw [coeffEmb_jq, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, PowerSeries.coe_pow]
    exact jqModC_mul_discriminant_expansion
  rw [realize_eq_div Γ hT f g _ hq τ hg]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
