import Dubon2026.SourceGammaOneFunctionFieldBaseChange
import Dubon2026.SourceOriginalFieldGeneration

/-! DUB-17/18 -> all-weight Galois association -> arithmetic realization of
finite Gamma1 Hecke characters -> actual Picard/H1 comparison -> regular
differential/cusp comparison. The scalar extension used for the actual curve
equals the field of literal integral modular-form ratios over the coefficient
field. This discharges the field-membership conversion in the converse
differential comparison without another scalar-extension framework.
The field-closure proof reuses SourceOriginalFieldGeneration. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField
open scoped MatrixGroups

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [Algebra ℚ L]
    (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  ext n
  rw [coeffEmb_coeff]
  simp only [intSeriesC, PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map]

theorem coeffEmb_image_intFormRatiosC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  ext x
  constructor
  · rintro ⟨y, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    apply mem_intFormRatiosC f g hf hg
    rw [← coeffEmb_intSeriesC]
    intro h
    apply hg0
    apply (coeffEmb L).injective
    simpa only [map_zero] using h
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hq : intSeriesC ℚ pg ≠ 0 := by
      intro h
      apply hg0
      rw [← coeffEmb_intSeriesC, h, map_zero]
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
      mem_intFormRatiosC f g hf hg hq, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem functionFieldOver_eq_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type*) [Field L] [Algebra ℚ L] :
    functionFieldOver Γ L = qExpFunctionFieldC L Γ := by
  apply le_antisymm
  · rw [functionFieldOver, laurentBaseChange, adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (qExpFunctionFieldC ℚ Γ).toSubfield := hx
    rw [qExpFunctionFieldC, adjoin_toSubfield] at hx'
    have hmem : coeffEmb L x ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪
          intFormRatiosC ℚ Γ)).map (coeffEmb L) := ⟨x, hx', rfl⟩
    rw [RingHom.map_field_closure] at hmem
    refine (Subfield.closure_le.2 ?_) hmem
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | hy
    · rw [coeffEmb_algebraMap]
      exact (qExpFunctionFieldC L Γ).algebraMap_mem _
    · apply intFormRatiosC_subset L Γ
      rw [← coeffEmb_image_intFormRatiosC Γ L]
      exact ⟨y, hy, rfl⟩
  · rw [qExpFunctionFieldC, adjoin_le_iff,
      ← coeffEmb_image_intFormRatiosC Γ L]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L
      (IntermediateField.subset_adjoin ℚ _ hy)

end
end Dubon2026.SourceFunctionField.GammaOne
