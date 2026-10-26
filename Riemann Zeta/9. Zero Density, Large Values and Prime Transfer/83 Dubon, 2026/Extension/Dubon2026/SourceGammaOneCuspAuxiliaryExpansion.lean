import Dubon2026.SourceGammaOneCuspAuxiliaryForm
import Dubon2026.SourceModularInverseJIntegral
import Dubon2026.SourceJEulerPolynomial

/-! DUB-17/18 -> actual Gamma1 differential comparison -> cusp integral
bound. Identify the genuine auxiliary form's expansion and retain the
constructed nonzero q-Euler normalization scalar. No exact Ramanujan
normalization or arbitrary complex-ratio field membership is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary
noncomputable section
open UpperHalfPlane ModularForm ModularNormPolynomial SourceDifferential
open scoped MatrixGroups
local notation "qL" => fun F : ℍ → ℂ => (qExpansion 1 F : LaurentSeries ℂ)

theorem qExpansion_Gform_mul
    (M : ℕ) [NeZero M] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) :
    qL (Gform M hΓ f : ℍ → ℂ) * qL ModularForm.discriminant =
      qL (f : ℍ → ℂ) ^ (2 * M) * qL (E₄ : ℍ → ℂ) ^ 3 := by
  have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    rintro A ⟨γ, _, rfl⟩
    exact ⟨γ, rfl⟩
  let dr : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    restrict hle (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  let er : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 4 := restrict hle E₄
  let fm : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 := f
  have hfun : ((Gform M hΓ f).mul dr : ℍ → ℂ) =
      ((fm.pow (2 * M)).mul (er.pow 3) : ℍ → ℂ) := by
    funext z
    simp only [ModularForm.coe_mul, ModularForm.coe_pow, Pi.mul_apply, Pi.pow_apply]
    change f z ^ (2 * M) * E₄ z ^ 3 / ModularForm.discriminant z *
      ModularForm.discriminant z = f z ^ (2 * M) * E₄ z ^ 3
    exact div_mul_cancel₀ _ (discriminant_ne_zero z)
  have hq := congrArg (fun F : ℍ → ℂ => (qExpansion 1 F : LaurentSeries ℂ)) hfun
  dsimp only at hq
  rw [ModularForm.qExpansion_mul one_pos (hper hT),
    ModularForm.qExpansion_mul one_pos (hper hT),
    ModularForm.qExpansion_pow one_pos (hper hT),
    ModularForm.qExpansion_pow one_pos (hper hT),
    PowerSeries.coe_mul, PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_pow] at hq
  exact hq

theorem cusp_expression_identity {K : Type*} [Field K]
    (N : ℕ) (F E S D θ Y j G C : K) (hE : E ≠ 0) (hD : D ≠ 0) (hC : C ≠ 0)
    (hθ : θ * D = C * (E ^ 2 * S)) (hY : Y * θ = F)
    (hj : j = E ^ 3 / D) (hES : E ^ 3 - S ^ 2 = 1728 * D)
    (hG : G * D = F ^ (2 * N) * E ^ 3) :
    Y ^ (2 * N) * j ^ (N + 1) * (j - 1728) ^ N = C⁻¹ ^ (2 * N) * (G / E ^ N) := by
  have hθ' : θ = C * (E ^ 2 * S) / D := (eq_div_iff hD).mpr hθ
  have hj' : j - 1728 = S ^ 2 / D := by
    rw [hj, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    linear_combination hES
  have h2 : Y ^ 2 * j * (j - 1728) = C⁻¹ ^ 2 * (F ^ 2 / E) := by
    rw [← hY, hθ', hj', hj]
    field_simp
  have hG' : G = F ^ (2 * N) * E ^ 3 / D := (eq_div_iff hD).mpr hG
  calc
    _ = (Y ^ 2 * j * (j - 1728)) ^ N * j := by
      rw [pow_mul, pow_succ, mul_pow, mul_pow]
      ring
    _ = (C⁻¹ ^ 2 * (F ^ 2 / E)) ^ N * (E ^ 3 / D) := by rw [h2, hj]
    _ = C⁻¹ ^ (2 * N) * (G / E ^ N) := by
      rw [hG', mul_pow, div_pow, ← pow_mul, ← pow_mul]
      field_simp

end
end Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary
