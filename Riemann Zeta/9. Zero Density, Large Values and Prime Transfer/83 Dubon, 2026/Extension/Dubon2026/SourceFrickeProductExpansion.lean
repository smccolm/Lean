import Dubon2026.SourceEisensteinRationalSeries
import Dubon2026.SourceFrickeTorsionConjugation

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> Fricke product coefficient transport.
The actual E4 E6 product is multiplied by the actual normalized Weierstrass
torsion function. Analytic expansion and coefficient transport are proved.
The elementary analytic assembly adapts anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache License 2.0. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open scoped Manifold MatrixGroups ModularForm

/-- The actual holomorphic Fricke numerator, before division by Delta. -/
def frickeH (N a₁ a₂ : ℕ) : ℍ → ℂ := (⇑E₄ * ⇑E₆ : ℍ → ℂ) * wpNorm N a₁ a₂

theorem periodic_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (frickeH N a₁ a₂ ∘ ofComplex) N := by
  have h4 := (periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL).nat_mul N
  have h6 := (periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL).nat_mul N
  have hw := periodic_wpNorm ha₁ ha₂ h0
  intro τ
  have e4 := h4 τ; have e6 := h6 τ; have ew := hw τ
  simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6 ew
  simp only [Function.comp_apply, frickeH, Pi.mul_apply, e4, e6, ew]

theorem mdifferentiable_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeH N a₁ a₂) :=
  (E₄.holo'.mul E₆.holo').mul (mdifferentiable_wpNorm ha₁ ha₂ h0)

theorem isBoundedAtImInfty_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (frickeH N a₁ a₂) :=
  ((ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆)).mul
    (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)


theorem qExpansion_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    qExpansion N (frickeH N a₁ a₂) =
      qExpansion N (⇑E₄ * ⇑E₆ : ℍ → ℂ) * qExpansion N (wpNorm N a₁ a₂) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact qExpansion_mul (analyticAt_cuspFunction_E4E6 (by omega))
    (analyticAt_cuspFunction_zero hN (periodic_wpNorm ha₁ ha₂ h₀)
      (mdifferentiable_wpNorm ha₁ ha₂ h₀) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h₀))

theorem hasSum_qExpansion_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion N (frickeH N a₁ a₂)).coeff m •
      Function.Periodic.qParam N τ ^ m) (frickeH N a₁ a₂ τ) :=
  hasSum_qExpansion (by exact_mod_cast (show 0 < N by omega)) (periodic_frickeH ha₁ ha₂ h0)
    (mdifferentiable_frickeH ha₁ ha₂ h0) (isBoundedAtImInfty_frickeH ha₁ ha₂ h0) τ


end
end Dubon2026.SourceFricke
