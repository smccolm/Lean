import Dubon2026.MatrixRepresentationDeterminant

/-! # The actual natural determinant family over all coefficient extensions -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R S T : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [CommRing T]

/-- The original representation's determinant over a specified coefficient extension. -/
def determinantCoefficientLaw (ρ : G →* GeneralLinearGroup ι R) (φ : R →+* S) :
    MonoidAlgebra S G →* S :=
  matrixRepresentationDeterminant ((GeneralLinearGroup.map φ).comp ρ)

/-- The actual coefficient-extension family is natural under every further coefficient map. -/
theorem determinantCoefficientLaw_natural (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (ψ : S →+* T) (x : MonoidAlgebra S G) :
    ψ (determinantCoefficientLaw ρ φ x) =
      determinantCoefficientLaw ρ (ψ.comp φ) (MonoidAlgebra.mapRingHom G ψ x) := by
  rw [determinantCoefficientLaw, matrixRepresentationDeterminant_map]
  rfl

/-- At every coefficient extension the original determinant family is homogeneous of its precise dimension. -/
theorem determinantCoefficientLaw_homogeneous (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (a : S) (x : MonoidAlgebra S G) :
    determinantCoefficientLaw ρ φ (a • x) =
      a ^ Fintype.card ι * determinantCoefficientLaw ρ φ x :=
  matrixRepresentationDeterminant_smul _ a x

/-- The whole coefficient-extension determinant family is multiplicative and normalized. -/
theorem determinantCoefficientLaw_multiplicative (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) :
    determinantCoefficientLaw ρ φ 1 = 1 ∧
      ∀ x y, determinantCoefficientLaw ρ φ (x * y) =
        determinantCoefficientLaw ρ φ x * determinantCoefficientLaw ρ φ y :=
  ⟨map_one _, map_mul _⟩

end
end Dubon2026
