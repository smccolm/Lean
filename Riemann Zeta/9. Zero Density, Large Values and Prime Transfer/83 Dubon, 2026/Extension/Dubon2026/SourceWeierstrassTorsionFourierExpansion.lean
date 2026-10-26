import Dubon2026.SourceWeierstrassTorsionFourierSum
import Dubon2026.SourceWeierstrassTorsionCuspBound

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> cyclotomic
Fricke expansions. The actual torsion expansion is regrouped by its
finite exponent fibers and identified with the native q-expansion.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
No external theorem module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

theorem qExpansion_wpNorm_coeff {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (wpNorm N a₁ a₂)).coeff n = wpQCoeff N a₁ a₂ n := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let f' : C(ℍ, ℂ) := ⟨wpNorm N a₁ a₂, (mdifferentiable_wpNorm ha₁ ha₂ h0).continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN (periodic_wpNorm ha₁ ha₂ h0)
      (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ wpQCoeff N a₁ a₂ m • Function.Periodic.qParam N τ ^ m)
      (f' τ) := by
    intro τ
    have h := hasSum_wpQCoeff (a₂ := a₂) ha₁ (τ := (τ : ℂ)) τ.im_pos
    rw [← wpNorm_eq ha₁ ha₂ h0] at h
    refine h.congr_fun fun m ↦ ?_
    simp only [smul_eq_mul, Function.Periodic.qParam, qN, Complex.ofReal_natCast]
  exact (qExpansion_coeff_unique f' hN hfan hf n).symm

theorem qExpansion_wpNorm_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N := by
  rw [qExpansion_wpNorm_coeff ha₁ ha₂ h0]
  exact wpQCoeff_mem_kN ha₁ a₂ n

theorem hasSum_qExpansion_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion N (wpNorm N a₁ a₂)).coeff m •
      Function.Periodic.qParam N τ ^ m) (wpNorm N a₁ a₂ τ) :=
  hasSum_qExpansion (by exact_mod_cast (show 0 < N by omega)) (periodic_wpNorm ha₁ ha₂ h0)
    (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0) τ


end
end Dubon2026.SourceFricke
