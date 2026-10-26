import Dubon2026.SourceGammaOneFunctionField

/-! DUB-17/18 -> all-weight arithmetic realization -> finite Gamma1 function
field. Every element of the actual rational q-expansion field is one ratio of
same-weight integral modular forms. This allows the bounded norm relation to
apply to every field element, not only the generators.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean,
JOneESRat.Ratio. Native strict-period equality is reused. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane IntermediateField HahnSeries
open scoped MatrixGroups
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

private theorem intSeriesC_add {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

section Ratio
variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem hper : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1


private theorem mul_mem_intFormRatiosC {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]


private theorem add_mem_intFormRatiosC {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (hper hT), ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos (hper hT), ModularForm.qExpansion_mul_coe one_pos (hper hT)]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]


omit hT in
private theorem inv_mem_intFormRatiosC {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]


private theorem algebraMap_mem_intFormRatiosC (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, PowerSeries.map_C]
    have : ((ModularForm.const (c.num : ℂ) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
        (c.num : ℂ) • ((1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
      funext z
      rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
        mul_one]
    rw [this, ModularForm.qExpansion_smul one_pos (hper hT), ModularForm.qExpansion_one,
      PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]
  · rw [IsIntegralQExp, PowerSeries.map_C]
    have : ((ModularForm.const (c.den : ℂ) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
        (c.den : ℂ) • ((1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
      funext z
      rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
        mul_one]
    rw [this, ModularForm.qExpansion_smul one_pos (hper hT), ModularForm.qExpansion_one,
      PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]
    push_cast
    rfl
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

theorem mem_qExpFunctionFieldC_iff {y : LaurentSeries ℚ} :
    y ∈ qExpFunctionFieldC ℚ Γ ↔ y ∈ intFormRatiosC ℚ Γ := by

  let R : IntermediateField ℚ (LaurentSeries ℚ) :=
    { carrier := intFormRatiosC ℚ Γ
      mul_mem' := fun ha hb => mul_mem_intFormRatiosC hT ha hb
      one_mem' := by simpa using algebraMap_mem_intFormRatiosC (Γ := Γ) hT 1
      add_mem' := fun ha hb => add_mem_intFormRatiosC hT ha hb
      zero_mem' := by simpa using algebraMap_mem_intFormRatiosC (Γ := Γ) hT 0
      algebraMap_mem' := fun c => algebraMap_mem_intFormRatiosC hT c
      inv_mem' := fun a ha => inv_mem_intFormRatiosC ha }
  have hle : qExpFunctionFieldC ℚ Γ ≤ R := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact ⟨fun h => hle h, fun h => intFormRatiosC_subset ℚ Γ h⟩

end Ratio

end
end Dubon2026.SourceFunctionField.GammaOne
