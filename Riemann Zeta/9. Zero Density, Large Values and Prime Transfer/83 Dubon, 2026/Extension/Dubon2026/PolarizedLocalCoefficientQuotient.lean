import Dubon2026.PolarizedResidualIdeal
import Dubon2026.LocalCoefficientReduction

/-! Residual-compatible source similitudes over the original coefficient
base give a local polarized quotient. This isolates the coefficient
compatibility used by the actual framed-ring consumer for DUB-17. -/

namespace Dubon2026
open Matrix

variable {G O R ι : Type*} [Group G] [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [Fintype ι] [DecidableEq ι]

/-- The actual residue map and original base similitude derive locality of the polarized quotient. -/
theorem representationPolarizedQuotient_isLocal_of_residue
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
    (σ : G →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
    (hτ : ∀ g, GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom (τ g) =
      polarizedBlockRepresentation (σ g))
    (ν : G →* Oˣ)
    (hν : ∀ g, polarizedSimilitude (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g)) :
    IsLocalRing (R ⧸ representationPolarizedIdeal τ (polarizedComponent.comp σ)
      ((Units.map (algebraMap O R)).comp ν)) := by
  apply representationPolarizedQuotient_isLocal _ _ _ (localCoefficientReduction eR).toRingHom σ hτ
  · intro g
    rfl
  · intro g
    rw [hν]
    apply Units.ext
    exact ((localCoefficientReduction eR).commutes (ν g : O)).symm

end Dubon2026
