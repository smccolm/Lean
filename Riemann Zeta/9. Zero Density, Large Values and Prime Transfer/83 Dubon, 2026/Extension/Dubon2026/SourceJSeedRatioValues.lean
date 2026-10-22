import Dubon2026.SourceOriginalAnalyticPlaceInvariance

/-! DUB-17/18 -> analytic finite-place geometry and differential realization.
The previous seed-ratio existence theorem exposes only its formal quotient.
Here the same explicit discriminant/E4 witnesses also expose their actual
pointwise values, needed to identify the original j-coordinate analytically.
All level changes will reuse the existing cusp degeneracy map.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem exists_jq_cusp_ratio_with_values :
    ∃ (g h : CuspForm (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) 24), h ≠ 0 ∧
      jqModC ℂ * (qExpansion 1 (h : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
        (qExpansion 1 (g : UpperHalfPlane → ℂ) : LaurentSeries ℂ) ∧
      (∀ τ : ℍ, g τ = ModularForm.discriminant τ * ModularForm.E₄ τ ^ 3) ∧
      (∀ τ : ℍ, h τ = ModularForm.discriminant τ * ModularForm.discriminant τ) := by
  let g : CuspForm 𝒮ℒ 24 := CuspForm.mcast (by norm_num)
    (CuspForm.discriminant.mulModularForm (ModularForm.E₄.pow 3))
  let h : CuspForm 𝒮ℒ 24 := CuspForm.discriminant.mulModularForm
    (CuspForm.toModularFormₗ CuspForm.discriminant)
  let g1 : CuspForm (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) 24 :=
    CuspForm.mcast rfl g gamma0_one_eq_SL
  let h1 : CuspForm (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) 24 :=
    CuspForm.mcast rfl h gamma0_one_eq_SL
  refine ⟨g1, h1, ?_, ?_, ?_, ?_⟩
  · intro he
    have hh := DFunLike.congr_fun he UpperHalfPlane.I
    change ModularForm.discriminant UpperHalfPlane.I * ModularForm.discriminant UpperHalfPlane.I = 0 at hh
    exact (mul_ne_zero (ModularForm.discriminant_ne_zero _) (ModularForm.discriminant_ne_zero _)) hh
  · have hqg : (qExpansion 1 (g1 : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
        (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) *
        (qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) : LaurentSeries ℂ) ^ 3 := by
      change (qExpansion 1 ((CuspForm.toModularFormₗ CuspForm.discriminant).mul
        (ModularForm.E₄.pow 3) : UpperHalfPlane → ℂ) : LaurentSeries ℂ) = _
      rw [ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, PowerSeries.coe_mul,
        PowerSeries.coe_pow]
      rfl
    have hqh : (qExpansion 1 (h1 : UpperHalfPlane → ℂ) : LaurentSeries ℂ) =
        (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) *
        (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) := by
      change (qExpansion 1 ((CuspForm.toModularFormₗ CuspForm.discriminant).mul
        (CuspForm.toModularFormₗ CuspForm.discriminant) : UpperHalfPlane → ℂ) : LaurentSeries ℂ) = _
      rw [ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL, PowerSeries.coe_mul]
      rfl
    rw [hqh, hqg, ← mul_assoc, jqModC_mul_discriminant_expansion, mul_comm]

  · intro τ; rfl
  · intro τ; rfl

end
end Dubon2026.SourceFunctionField
