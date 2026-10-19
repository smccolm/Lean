import Dubon2026.FramedCoefficientClassification
import Dubon2026.FramedCoefficientRingCompatibility

/-! Assemble the two inverse coefficient maps from four constructed
classifications, each carrying its own matrix-evaluation proof. This
keeps the large actual arithmetic rings out of repeated projection and
evaluation elaboration. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

variable {ι O R S : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
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
  (CSS : FramedCoefficientClassification eS eS H σ δ π τS)

/-- The four constructed classifications provide the two actual
inverse algebra maps over the original coefficient ring. -/
def framedCoefficientClassificationRingEquiv : S ≃ₐ[O] R :=
  framedCoefficientRingEquiv eR eS H π hπ σ δ τR τS
    CRR.equiv CRS.equiv CSR.equiv CSS.equiv
    CRR.evaluation CRS.evaluation CSR.evaluation CSS.evaluation

/-- The assembled isomorphism preserves the original residue maps
and all universal matrices used in the four classifications. -/
theorem framedCoefficientClassificationRingEquiv_compatible :
    (localCoefficientReduction eR).comp
      (framedCoefficientClassificationRingEquiv eR eS H π hπ σ δ τR τS CRR CRS CSR CSS).toAlgHom =
        localCoefficientReduction eS ∧
    ∀ g, GeneralLinearGroup.map
      (framedCoefficientClassificationRingEquiv eR eS H π hπ σ δ τR τS CRR CRS CSR CSS).toAlgHom.toRingHom
        (τS g) = τR g :=
  framedCoefficientRingEquiv_compatible eR eS H π hπ σ δ τR τS
    CRR.equiv CRS.equiv CSR.equiv CSS.equiv
    CRR.evaluation CRS.evaluation CSR.evaluation CSS.evaluation

end
end Dubon2026
