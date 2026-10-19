import Dubon2026.OriginalCoefficientFramedEquivalence

/-! A constructed framed classification together with its literal
universal-matrix evaluation. Keeping these outputs together prevents
repeated unfolding of the large arithmetic source ring when assembling
the original-support ring comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- Output of a coefficient classification: the actual equivalence
and its proved evaluation on every original universal matrix. Actual
arithmetic constructors below derive both fields from existing proofs. -/
structure FramedCoefficientClassification
    {ι O R A : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eA : ResidueField A ≃ₐ[O] ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (ResidueField O)) (δ : H →* Oˣ)
    (π : G → H) (τ : G → GeneralLinearGroup ι R) where
  /-- The proved classification of residue-preserving coefficient maps. -/
  equiv : {f : R →ₐ[O] A //
    (localCoefficientReduction eA).comp f = localCoefficientReduction eR} ≃
      {f : OriginalContinuousFramedFiber eA H σ //
        ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O A) (δ h)}
  /-- Classification evaluates the original universal matrix by the coefficient map. -/
  evaluation : ∀ f g, (equiv f).val.val (π g) = GeneralLinearGroup.map f.val.toRingHom (τ g)

end
end Dubon2026
