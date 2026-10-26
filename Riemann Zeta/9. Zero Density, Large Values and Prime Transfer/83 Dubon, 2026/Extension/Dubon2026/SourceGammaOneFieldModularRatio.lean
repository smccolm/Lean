import Dubon2026.SourceGammaOneModularRatios
import Dubon2026.SourceGammaOneScalarExtension

/-! DUB-17/18 -> actual Picard/H1 comparison -> regular differential/cusp
comparison. Every element of the actual Gamma1 complex function field has
an equal-weight modular quotient. This supplies the analytic presentation
needed by the integral-bound-to-cusp construction. No ratio is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem isRatio_of_mem_qExpFunctionFieldC
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    (hT : ModularGroup.T ∈ Γ) {x : LaurentSeries ℂ}
    (hx : x ∈ qExpFunctionFieldC ℂ Γ) :
    ModularRatios.IsRatio Γ x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      have hpf : intSeriesC ℂ pf = ModularRatios.qL f := by
        exact congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hf
      have hpg : intSeriesC ℂ pg = ModularRatios.qL g := by
        exact congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hg
      have hqg : ModularRatios.qL g ≠ 0 := by rwa [← hpg]
      have hg' : g ≠ 0 := by
        intro hz
        apply hqg
        simp only [hz, ModularRatios.qL, ModularForm.coe_zero, qExpansion_zero,
          PowerSeries.coe_zero]
      refine ⟨k, f, g, hg', ?_⟩
      rw [hpf, hpg, div_mul_cancel₀ _ hqg]
  | algebraMap c => exact ModularRatios.isRatio_algebraMap hT c
  | add _ _ _ _ hx hy => exact ModularRatios.IsRatio.add hT hx hy
  | inv _ _ hx => exact ModularRatios.IsRatio.inv hT hx
  | mul _ _ _ _ hx hy => exact ModularRatios.IsRatio.mul hT hx hy

theorem functionFieldOver_modular_ratio
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    (hT : ModularGroup.T ∈ Γ) (x : functionFieldOver Γ ℂ) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) *
        (qExpansion 1 (h : ℍ → ℂ) : LaurentSeries ℂ) =
          (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ) := by
  apply isRatio_of_mem_qExpFunctionFieldC hT
  simpa only [functionFieldOver_eq_qExpFunctionFieldC] using x.2

end
end Dubon2026.SourceFunctionField.GammaOne
