import Dubon2026.SourceJEulerModularIdentity

/-! DUB-17/18 -> actual Gamma1 differential comparison -> finite-coordinate
integrality. Transport the existing analytic level-one derivative and
discriminant identities to the literal Laurent series. The nonzero scalar
is constructed by the proved weight-14 dimension theorem, not assumed. -/
namespace Dubon2026.SourceFunctionField.ModularQDerivative
noncomputable section
open UpperHalfPlane ModularForm SourceDifferential
open scoped MatrixGroups
local notation "δ" => (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ)
local notation "e₄" => (qExpansion 1 (E₄ : ℍ → ℂ) : LaurentSeries ℂ)
local notation "e₆" => (qExpansion 1 (E₆ : ℍ → ℂ) : LaurentSeries ℂ)

theorem laurent_discriminant_relation : (1728 : LaurentSeries ℂ) * δ = e₄ ^ 3 - e₆ ^ 2 := by
  let d : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  let a : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let b : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have h : (1728 : ℂ) • d = a - b := by
    ext z
    change (1728 : ℂ) * ModularForm.discriminant z = E₄ z ^ 3 - E₆ z ^ 2
    have hd := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
    linear_combination 1728 * hd
  have hq := congrArg (fun f : ModularForm 𝒮ℒ 12 =>
    (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) h
  dsimp only at hq
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_smul, PowerSeries.coe_sub,
    ← HahnSeries.single_zero_mul_eq_smul,
    ← algebraMap_laurentSeries_apply_alt] at hq
  simpa only [a, b, d, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_pow, map_ofNat] using hq

theorem exists_qEuler_jqModC_formula :
    ∃ c : ℂ, c ≠ 0 ∧
      qEuler ℂ (jqModC ℂ) * δ = algebraMap ℂ (LaurentSeries ℂ) c * (e₄ ^ 2 * e₆) := by
  obtain ⟨c, hc, he⟩ := JMultiplicity.exists_D_jf_mul_Δ_eq
  have hform : JMultiplicity.g14 = c • JMultiplicity.e14 := by
    ext z
    change JMultiplicity.g14 z = c * JMultiplicity.e14 z
    rw [JMultiplicity.g14_apply, JMultiplicity.e14_apply]
    exact he z
  refine ⟨c, hc, ?_⟩
  rw [qEuler_jqModC_mul_discriminant, hform, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coe_smul,
    ← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_apply_alt]
  congr 1
  simp only [JMultiplicity.e14, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_mul, pow_two]

theorem exists_qEuler_jqModC_power_six :
    ∃ c : ℂ, c ≠ 0 ∧
      qEuler ℂ (jqModC ℂ) ^ 6 =
        algebraMap ℂ (LaurentSeries ℂ) c ^ 6 *
          (jqModC ℂ) ^ 4 * (jqModC ℂ - 1728) ^ 3 * δ := by
  obtain ⟨c, hc, he⟩ := exists_qEuler_jqModC_formula
  refine ⟨c, hc, ?_⟩
  have hd := discriminant_expansion_ne_zero
  have hj : jqModC ℂ - 1728 = e₆ ^ 2 / δ := by
    rw [jqModC_eq_modular_quotient, eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]
    linear_combination -laurent_discriminant_relation
  have he' : qEuler ℂ (jqModC ℂ) = algebraMap ℂ (LaurentSeries ℂ) c * (e₄ ^ 2 * e₆) / δ :=
    (eq_div_iff hd).mpr he
  rw [he', hj, jqModC_eq_modular_quotient]
  field_simp

end
end Dubon2026.SourceFunctionField.ModularQDerivative
