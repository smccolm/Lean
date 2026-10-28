import Dubon2026.SourceSmoothComparisonCusps
import Dubon2026.SourceModularParabolicWindingLog

/-! DUB-17/18 -> full all-weight arithmetic association -> original Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> winding logarithm
of the actual filled comparison quotient. Equal local orders, finite divisor
support, the actual invariances and cusp data discharge all logarithm inputs.
The source punctured-limit convention and derivative decay are retained.
No logarithm, integer character or parabolicity certificate is assumed. -/
namespace Dubon2026.SourceSmoothComparison
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set SourceSmoothDivisor
open scoped MatrixGroups Topology Real

theorem exists_filled_winding_log (Γ : Subgroup SL(2, ℤ)) (S : Finset ℍ) (n : ℍ → ℤ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, γ.val • s = τ)
    {Φ V : ℂ → ℂ} (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n)
    (hinvΦ : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hinvV : ∀ γ ∈ Γ, ∀ τ : ℍ, V ((γ • τ : ℍ) : ℂ) = V τ)
    (hV1 : ∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V (sm σ z) = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto
      (fun τ : ℍ => fderiv ℝ (fun u : ℂ => Φ (sm σ u)) (τ : ℂ)) atImInfty (𝓝 0)) :
    (∀ τ : ℍ, quot Φ V τ = limUnder (𝓝[≠] (τ : ℂ)) (fun w => Φ w / V w)) ∧
    (∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => quot Φ V ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c) ∧
      Tendsto (fun τ : ℍ => fderiv ℝ (fun u : ℂ => quot Φ V (sm σ u)) (τ : ℂ))
        atImInfty (𝓝 0)) ∧
    ∃ (L : ℂ → ℂ) (m : Additive Γ →+ ℤ),
      (∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → m (Additive.ofMul γ) = 0) ∧
      (∀ τ : ℍ, ContDiffAt ℝ 1 L τ) ∧
      (∀ τ : ℍ, HasFDerivAt L ((quot Φ V τ)⁻¹ • fderiv ℝ (quot Φ V) τ) τ) ∧
      (∀ τ : ℍ, Complex.exp (L τ) = quot Φ V τ) ∧
      (∀ (γ : Γ) (τ : ℍ), L (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        L τ + 2 * π * Complex.I * (m (Additive.ofMul γ) : ℂ)) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ,
        Tendsto (fun τ : ℍ => L ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) := by
  have hqc := quot_cusp_data S n hcov hΦ hV hV1 hcusp hdecay
  refine ⟨quot_eq_limUnder hΦ hV, hqc, ?_⟩
  apply SourceWindingLog.exists_parabolic_log Γ (quot Φ V)
    (contDiffAt_quot hΦ hV) (quot_ne_zero hΦ hV)
    (fun _ hγ τ => quot_smul hΦ hV hinvΦ hinvV hγ τ)
  intro σ
  obtain ⟨c, hc, hlim, _⟩ := hqc σ
  exact ⟨c, hc, hlim⟩

end
end Dubon2026.SourceSmoothComparison
