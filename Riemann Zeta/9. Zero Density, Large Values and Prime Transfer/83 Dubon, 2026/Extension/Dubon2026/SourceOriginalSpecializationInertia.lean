import Dubon2026.SourceOriginalTateInertia
import Dubon2026.SourceOriginalPrimitiveGaloisRealization

/-! DUB-17/18 -> original primitive weight-two Galois association ->
unramifiedness of the actual specialization. The image of the proved
specialization spans its coefficient space. Native linear-map extensionality
on that span transfers the derived rational Tate inertia identity to the
same specialized representation. No new scalar or representation framework
and no Frobenius identity are assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]

theorem original_specialization_inertia_identity
    {E : Type*} [Field E] [Algebra ℚ_[ell] E]
    (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x))
    (A : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hNp : ¬p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    ρ τ = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on_range hspan
  intro x
  change (ρ τ).val *ᵥ π x = (1 : Matrix (Fin 2) (Fin 2) E) *ᵥ π x
  rw [hact, (GaussReduction.originalTateGaloisRep_eq_one_away_level_prime A N ell p hp hNp hA τ hτ).2]
  simp

end
end Dubon2026.SourceFunctionField.OriginalChart
