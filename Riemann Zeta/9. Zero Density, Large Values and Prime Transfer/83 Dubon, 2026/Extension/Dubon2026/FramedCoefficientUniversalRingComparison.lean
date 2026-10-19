import Dubon2026.ResidueMatrixRingComparison

/-! Apply the two proved classification families before specializing
to the actual coefficient rings. The two self-evaluations and two
cross-evaluations occur over abstract complete local rings in this
checked assembly, avoiding repeated expansion of the large arithmetic
ring definitions at the use site. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- Two actual classification families construct the inverse ring
maps by their own identity coefficient points, retaining residue and
universal-matrix compatibility. -/
def framedCoefficientUniversalRingComparison
    {ι O R S : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [WithIdeal R] [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [WithIdeal S] [IsAdicComplete (maximalIdeal S) S]
    (hR : (WithIdeal.i : Ideal R) = maximalIdeal R)
    (hS : (WithIdeal.i : Ideal S) = maximalIdeal S)
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (H : ProfiniteGrp.{u}) (π : G → H) (hπ : Function.Surjective π)
    (σ : H →* GeneralLinearGroup ι (ResidueField O)) (δ : H →* Oˣ)
    (τR : G → GeneralLinearGroup ι R) (τS : G → GeneralLinearGroup ι S)
    (FR : ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]
      (_hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
      (eA : ResidueField A ≃ₐ[O] ResidueField O),
      FramedCoefficientClassification eR eA H σ δ π τR)
    (FS : ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]
      (_hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
      (eA : ResidueField A ≃ₐ[O] ResidueField O),
      FramedCoefficientClassification eS eA H σ δ π τS) :
    ResidueMatrixRingComparison eR eS τR τS :=
  framedCoefficientClassificationRingComparison eR eS H π hπ σ δ τR τS
    (FR hR eR) (FR hS eS) (FS hR eR) (FS hS eS)

end
end Dubon2026
