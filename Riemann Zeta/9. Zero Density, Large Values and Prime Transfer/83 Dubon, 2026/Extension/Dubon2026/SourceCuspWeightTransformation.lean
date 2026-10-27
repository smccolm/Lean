import Dubon2026.SourceCuspWeightFactors

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. Reuse the existing original E4, E6
and discriminant transformation laws to prove the weight-balanced slash
identity. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm
local notation "Δ" => ModularForm.discriminant

theorem eisensteinFactor_smul (a b : ℕ) (A : SL(2, ℤ)) (τ : ℍ) :
    eisensteinFactor a b (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) * eisensteinFactor a b τ := by
  simp only [eisensteinFactor, JMultiplicity.E₄_smul, JMultiplicity.E₆_smul, zpow_natCast, zpow_ofNat]
  ring

theorem discriminant_pow_smul (m : ℕ) (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) ^ m = denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ) * Δ τ ^ m := by
  rw [JMultiplicity.Δ_smul, zpow_natCast, zpow_ofNat]
  ring

theorem slash_mul_eisensteinFactor {k : ℤ} {a b m : ℕ}
    (hk : k + 4 * a + 6 * b = 12 * m) {F f : ℍ → ℂ} (hf : ∀ τ : ℍ, f τ * eisensteinFactor a b τ = F τ * Δ τ ^ m)
    (A : SL(2, ℤ)) (τ : ℍ) : (f ∣[k] A) τ * eisensteinFactor a b τ = F (A • τ) * Δ τ ^ m := by
  have hd : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ≠ 0 := denom_ne_zero _ _
  have h1 := hf (A • τ)
  rw [eisensteinFactor_smul, discriminant_pow_smul] at h1
  rw [ModularForm.SL_slash_apply]

  have hexp : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ (-k) =
      denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) *
        (denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ))⁻¹ := by
    rw [← zpow_neg, ← zpow_add₀ hd]
    congr 1
    push_cast
    linarith
  rw [hexp]
  have h12 : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ ((12 * m : ℕ) : ℤ) ≠ 0 := zpow_ne_zero _ hd
  field_simp
  linear_combination h1

end
end Dubon2026.SourceFunctionField.CuspWeightCriterion
