import Dubon2026.AuxiliaryFamilyAugmentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! Actual character data and a coefficient-preserving algebra
identification of its augmentation quotient. The constructor below
derives the identification from the proved equality of original ideals;
this record is output data, never an assumed specialization certificate. -/

namespace Dubon2026
noncomputable section

/-- An actual auxiliary character family whose augmentation quotient
is the displayed original quotient, with every coefficient class fixed. -/
structure AuxiliaryFamilyAugmentationSpecialization
    (O : Type*) [CommRing O] {S ι R : Type*} [Fintype S] [Fintype ι]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    (D : S → Type*) [∀ s, Group (D s)] (J : Ideal R) where
  /-- The constructed family of auxiliary coefficient characters. -/
  characters : ∀ s, D s →* (ι → R)ˣ
  /-- Every coordinate character reduces to one in the actual residue field. -/
  residue_one : ∀ s d i, IsLocalRing.residue R ((characters s d).val i) = 1
  /-- The character augmentation quotient identifies with the original inertia quotient. -/
  equiv : (R ⧸ auxiliaryFamilyAugmentationIdeal O characters) ≃ₐ[O] R ⧸ J
  /-- The identification fixes the class of every original coefficient. -/
  equiv_mk : ∀ r : R,
    equiv (Ideal.Quotient.mk (auxiliaryFamilyAugmentationIdeal O characters) r) =
      Ideal.Quotient.mk J r

/-- The exact original ideal equality constructs the actual
coefficient-preserving augmentation specialization. -/
theorem auxiliaryFamilyAugmentationSpecialization_of_exists
    (O : Type*) [CommRing O] {S ι R : Type*} [Fintype S] [Fintype ι]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    (D : S → Type*) [∀ s, Group (D s)] (J : Ideal R)
    (h : ∃ κ : ∀ s, D s →* (ι → R)ˣ,
      (∀ s d i, IsLocalRing.residue R ((κ s d).val i) = 1) ∧
      auxiliaryFamilyAugmentationIdeal O κ = J) :
    Nonempty (AuxiliaryFamilyAugmentationSpecialization O (ι := ι) D J) := by
  obtain ⟨κ, hκ, hJ⟩ := h
  exact ⟨⟨κ, hκ, Ideal.quotientEquivAlgOfEq O hJ, Ideal.quotientEquivAlgOfEq_mk O hJ⟩⟩

end
end Dubon2026
