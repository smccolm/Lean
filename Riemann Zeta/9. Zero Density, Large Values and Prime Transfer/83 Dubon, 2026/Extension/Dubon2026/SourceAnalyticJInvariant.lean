import Dubon2026.SourceModularJSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! DUB-17/18 -> original parabolic Hecke realization -> cusp-form lower
dimension bound -> differential expansion -> finite original function-field
extension -> modular polynomial relations -> analytic realization of the
literal j Laurent series. Pinned Eisenstein coefficients, the actual analytic
discriminant and its convergent product are used. Formal principal coefficients
alone are not treated as analytic modularity or as a field-degree proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_E4_cube_div_discriminant_smul.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology ModularForm OnePoint
local notation "𝕢" => Function.Periodic.qParam

theorem E4_cube_div_discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE : ModularForm.E₄ (γ • τ) = denom (mapGL ℝ γ) τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) hγ τ
  have hΔ : ModularForm.discriminant (γ • τ)
      = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
    simp only [CuspForm.coe_discriminant] at this
    exact this
  have hd : denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [hE, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  norm_num
  rw [mul_div_mul_left _ _ (zpow_ne_zero 12 hd)]

end
end Dubon2026.SourceFunctionField
