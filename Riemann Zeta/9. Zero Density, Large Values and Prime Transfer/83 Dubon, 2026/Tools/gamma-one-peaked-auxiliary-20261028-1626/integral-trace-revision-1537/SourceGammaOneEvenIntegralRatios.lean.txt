import Dubon2026.SourceGammaOneRatioClosure

/-! DUB-17/18 -> original all-weight association -> original Gamma1 degree
preservation -> reduced field action -> slash integrality of the original
integral-ratio generators. Every generator f/g is (f*g)/(g*g), with even
weight and the same literal Laurent series. Thus an even-weight integrality
route suffices for this field action; the odd-weight auxiliary-form branch
of the external general theorem is unnecessary. This does not establish
slash integrality itself or replace the original function field. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem exists_even_integral_ratio {K : Type*} [Field K]
    {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    {x : LaurentSeries K} (hx : x ∈ intFormRatiosC K Γ) :
    ∃ (k : ℤ), Even k ∧
      ∃ (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ), IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧
          intSeriesC K pg ≠ 0 ∧ x = intSeriesC K pf / intSeriesC K pg := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  refine ⟨k + k, ⟨k, rfl⟩, f.mul g, g.mul g, pf * pg, pg * pg, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) f g).symm
  · rw [IsIntegralQExp, map_mul, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) g g).symm
  · rw [intSeriesC_mul]
    exact mul_ne_zero hg0 hg0
  · rw [intSeriesC_mul, intSeriesC_mul]
    field_simp

theorem exists_even_integral_ratio_of_original_field
    {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
    (x : qExpFunctionFieldC ℚ Γ) :
    ∃ (k : ℤ), Even k ∧
      ∃ (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ), IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧
          intSeriesC ℚ pg ≠ 0 ∧ (x : LaurentSeries ℚ) = intSeriesC ℚ pf / intSeriesC ℚ pg :=
  exists_even_integral_ratio hT ((mem_qExpFunctionFieldC_iff hT).mp x.property)

end
end Dubon2026.SourceFunctionField.GammaOne
