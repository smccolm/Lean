import Dubon2026.SourceOriginalSpecializationInertia
import Dubon2026.SourceSpanningSpecializationQuadratic

/-! DUB-17/18 -> Frobenius polynomial of the same primitive-form
realization. The actual rational Tate quadratic identity transfers along
the proved spanning specialization, using its literal Hecke eigenvalue and
original arithmetic intertwining. The narrower Tate quadratic identity is
explicit here and will be supplied by the original Frobenius consumer.
No determinant or characteristic-polynomial conclusion is asserted. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]

theorem original_specialization_quadratic
    {E : Type*} [Field E] [Algebra ℚ_[ell] E]
    (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x))
    (p : ℕ) [NeZero p] (a : E)
    (hhecke : ∀ x : originalRationalTateModule N ell,
      π ((TateModule.tateMap ell (originalHeckePicard Qbar N p)).baseChange ℚ_[ell] x) = a • π x)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hquad : (TateModule.tateMap ell (originalHeckePicard Qbar N p)).baseChange ℚ_[ell] *
        originalRationalTateGaloisRep N ell τ =
      originalRationalTateGaloisRep N ell τ * originalRationalTateGaloisRep N ell τ + p • 1) :
    (ρ τ).val * (ρ τ).val + p • (1 : Matrix (Fin 2) (Fin 2) E) = a • (ρ τ).val := by
  exact quadratic_identity_on_spanning_specialization π (ρ τ).val
    (originalRationalTateGaloisRep N ell τ)
    ((TateModule.tateMap ell (originalHeckePicard Qbar N p)).baseChange ℚ_[ell])
    a p hspan (hact τ) hhecke hquad

end
end Dubon2026.SourceFunctionField.OriginalChart
