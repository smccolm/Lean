import Dubon2026.SourceOriginalSpecializationInertia
import Dubon2026.SourceOriginalPrimitiveResidualRealization
import Dubon2026.SourceIntegralMatrixCharpoly

/-! DUB-17/18 -> actual residual association. The same original
inertia identity passes through the existing integral basis comparison
and the literal entrywise residue map; no local action is replaced. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open SourceCurve Matrix
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
variable {E : Type} [Field E] [Algebra ℚ_[ell] E] [ValuativeRel E]

theorem original_residual_inertia_identity
    (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x))
    (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (ρint : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝒪[E])
    (ρres : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝓀[E])
    (hres : ∀ σ i j, (ρres σ).val i j = IsLocalRing.residue 𝒪[E] ((ρint σ).val i j))
    (hfield : ∀ σ v, (ρint σ).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ σ).val *ᵥ v))
    (A : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hNp : ¬p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hσ : σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    ρ σ = 1 ∧ ρint σ = 1 ∧ ρres σ = 1 := by
  have hi := original_specialization_inertia_identity N ell π ρ hspan hact A p hp hNp hA σ hσ
  have h := residue_matrix_one_of_intertwiner (algebraMap 𝒪[E] E)
    Subtype.val_injective (IsLocalRing.residue 𝒪[E]) (ρint σ).val (ρres σ).val e
    (fun v => by simpa [hi] using hfield σ v) (hres σ)
  exact ⟨hi, Units.ext h.1, Units.ext h.2⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
