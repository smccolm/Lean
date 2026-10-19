import Dubon2026.FramedCoefficientClassificationRingEquiv

/-! A constructed ring identification with the exact residue and
universal-matrix compatibility retained in its output. This output is
used for the actual original-support augmentation specialization. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- The actual algebra isomorphism and its proved coefficient and
matrix compatibilities. This is constructed output, never an assumed
arithmetic comparison certificate. -/
structure ResidueMatrixRingComparison
    {ι O R S : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing S] [IsLocalRing S] [Algebra O S]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (τR : G → GeneralLinearGroup ι R) (τS : G → GeneralLinearGroup ι S) where
  /-- The constructed isomorphism of the two actual coefficient algebras. -/
  equiv : S ≃ₐ[O] R
  /-- The isomorphism commutes with their specified residue maps. -/
  residue : (localCoefficientReduction eR).comp equiv.toAlgHom = localCoefficientReduction eS
  /-- The isomorphism identifies every original universal matrix. -/
  evaluation : ∀ g, GeneralLinearGroup.map equiv.toAlgHom.toRingHom (τS g) = τR g

/-- The four actual classifications construct a coefficient
isomorphism preserving the residue and every universal matrix. -/
def framedCoefficientClassificationRingComparison
    {ι O R S : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [WithIdeal R]
    [CommRing S] [IsLocalRing S] [Algebra O S] [WithIdeal S]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (H : ProfiniteGrp.{u}) (π : G → H) (hπ : Function.Surjective π)
    (σ : H →* GeneralLinearGroup ι (ResidueField O)) (δ : H →* Oˣ)
    (τR : G → GeneralLinearGroup ι R) (τS : G → GeneralLinearGroup ι S)
    (CRR : FramedCoefficientClassification eR eR H σ δ π τR)
    (CRS : FramedCoefficientClassification eR eS H σ δ π τR)
    (CSR : FramedCoefficientClassification eS eR H σ δ π τS)
    (CSS : FramedCoefficientClassification eS eS H σ δ π τS) :
    ResidueMatrixRingComparison eR eS τR τS := by
  let e := framedCoefficientClassificationRingEquiv eR eS H π hπ σ δ τR τS CRR CRS CSR CSS
  have h := framedCoefficientClassificationRingEquiv_compatible eR eS H π hπ σ δ τR τS CRR CRS CSR CSS
  exact ⟨e, h.1, h.2⟩

end
end Dubon2026
