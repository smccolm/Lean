import Dubon2026.SourceGammaOneMultiplierUnitarization
import Dubon2026.SourceGammaOneUnitaryDivisorPrincipal

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi principal-divisor
converse. Consume the proved normalization of an actual meromorphic
multiplier to discharge unit modulus in the original principal-divisor
consumer. The actual meromorphic function, its orders and nonzero cusp
limits remain explicit construction obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open Matrix.SpecialLinearGroup SourceSmoothedUnfolding
open scoped MatrixGroups Topology Real Classical ComplexConjugate GammaOne

theorem analytic_divisor_isPrincipal_of_meromorphic_multiplier (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ))
    (hclass : c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) ∈
      sourceWeightTwoIntegralLattice (Gamma1 N)) :
    Divisor.IsPrincipal (Finsupp.mapDomain (analyticPlace hT) c) := by
  obtain ⟨F₁, χ₁, hF₁, hχ₁, hunit, hcusp₁, horder⟩ :=
    exists_unitary_multiplier_same_orders N F χ hF hχ hcusp
  apply analytic_divisor_isPrincipal_of_unitary_meromorphic_function
    N hT c hc F₁ χ₁ hF₁ hχ₁ hunit hcusp₁ _ hclass
  intro τ
  exact (horder τ).trans (ho τ)

end
end Dubon2026.SourceFunctionField.GammaOne
