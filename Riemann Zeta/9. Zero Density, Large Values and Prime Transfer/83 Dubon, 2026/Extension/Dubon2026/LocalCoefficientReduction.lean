import Dubon2026.ResidualRepresentationCoordinates

/-! # Genuine reduction of local coefficient algebras with an identified residue field -/

namespace Dubon2026

noncomputable section

variable {O A : Type*} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]

/-- The actual residue map of the original local coefficient algebra followed by its specified residue-field identification. -/
def localCoefficientReduction
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    A →ₐ[O] IsLocalRing.ResidueField O :=
  e.toAlgHom.comp (IsScalarTower.toAlgHom O A (IsLocalRing.ResidueField A))

/-- The genuine coefficient reduction vanishes precisely on the actual coefficient maximal ideal. -/
theorem localCoefficientReduction_eq_zero_iff
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) (x : A) :
    localCoefficientReduction e x = 0 ↔ x ∈ IsLocalRing.maximalIdeal A := by
  change e (IsLocalRing.residue A x) = 0 ↔ _
  rw [EmbeddingLike.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]

/-- Nonzero genuine reduction is equivalent to being a unit in the original local coefficient algebra. -/
theorem localCoefficientReduction_ne_zero_iff
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) (x : A) :
    localCoefficientReduction e x ≠ 0 ↔ IsUnit x := by
  change e (IsLocalRing.residue A x) ≠ 0 ↔ _
  rw [ne_eq, EmbeddingLike.map_eq_zero_iff]
  exact IsLocalRing.residue_ne_zero_iff_isUnit x

/-- The actual coefficient reduction is surjective onto the original residue field. -/
theorem localCoefficientReduction_surjective
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Surjective (localCoefficientReduction e) :=
  e.surjective.comp IsLocalRing.residue_surjective

end
end Dubon2026
