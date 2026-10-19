import Dubon2026.AuxiliaryFamilyAugmentationSpecialization
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The actual augmentation specialization transports universal
matrices through the constructed coefficient isomorphism. The output
record retains the real character family, residue and full matrix
comparison needed in the arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- Constructed character augmentation data identifying the quotient
with the displayed coefficient ring and preserving every specified
universal matrix. This is output data, not an assumed certificate. -/
structure AuxiliaryFamilyAugmentationRepresentationComparison
    (O : Type*) [CommRing O] {S ι n G R A : Type*}
    [Fintype S] [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
    (D : S → Type*) [∀ s, Group (D s)]
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A) where
  /-- The constructed auxiliary characters on the actual coefficient ring. -/
  characters : ∀ s, D s →* (ι → R)ˣ
  /-- Each original residue character is trivial. -/
  residue_one : ∀ s d i, IsLocalRing.residue R ((characters s d).val i) = 1
  /-- The augmentation quotient recovers the displayed coefficient algebra. -/
  equiv : (R ⧸ auxiliaryFamilyAugmentationIdeal O characters) ≃ₐ[O] A
  /-- Reduction and specialization identify every specified universal matrix. -/
  matrix : ∀ g, GeneralLinearGroup.map equiv.toAlgHom.toRingHom
    (GeneralLinearGroup.map (Ideal.Quotient.mk (auxiliaryFamilyAugmentationIdeal O characters))
      (τ g)) = τ₀ g

/-- Compose the actual augmentation-to-inertia isomorphism with an
actual coefficient ring comparison. Equality on every original
coefficient class proves equality on the entire universal matrices. -/
def auxiliaryFamilyAugmentationRepresentationComparison
    (O : Type*) [CommRing O] {S ι n G R A : Type*}
    [Fintype S] [Fintype ι] [Fintype n] [DecidableEq n]
    [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
    (D : S → Type*) [∀ s, Group (D s)] (J : Ideal R)
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)
    (d : AuxiliaryFamilyAugmentationSpecialization O (ι := ι) D J)
    (e : (R ⧸ J) ≃ₐ[O] A)
    (he : ∀ g, GeneralLinearGroup.map e.toAlgHom.toRingHom
      (GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g)) = τ₀ g) :
    AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι) D τ τ₀ where
  characters := d.characters
  residue_one := d.residue_one
  equiv := d.equiv.trans e
  matrix g := by
    have hd : GeneralLinearGroup.map d.equiv.toAlgHom.toRingHom
        (GeneralLinearGroup.map (Ideal.Quotient.mk (auxiliaryFamilyAugmentationIdeal O d.characters))
          (τ g)) = GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g) := by
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact d.equiv_mk ((τ g).val i j)
    change GeneralLinearGroup.map (e.toAlgHom.toRingHom.comp d.equiv.toAlgHom.toRingHom) _ = _
    rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hd]
    exact he g

end
end Dubon2026
