import Dubon2026.FramedCoefficientRingEquiv

/-! The constructed inverse ring maps preserve the original residue
identification and every actual universal matrix. These identities are
needed when the auxiliary augmentation comparison is assembled. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- The constructed coefficient ring isomorphism is compatible with
the original residue maps and universal-matrix evaluation. -/
theorem framedCoefficientRingEquiv_compatible
    {ι O R S : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [WithIdeal R]
    [CommRing S] [IsLocalRing S] [Algebra O S] [WithIdeal S]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (H : ProfiniteGrp.{u}) (π : G → H) (hπ : Function.Surjective π)
    (σ : H →* GeneralLinearGroup ι (ResidueField O)) (δ : H →* Oˣ)
    (τR : G → GeneralLinearGroup ι R) (τS : G → GeneralLinearGroup ι S)
    (ERR : {f : R →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eR} ≃
        {f : OriginalContinuousFramedFiber eR H σ //
          ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O R) (δ h)})
    (ERS : {f : R →ₐ[O] S //
      (localCoefficientReduction eS).comp f = localCoefficientReduction eR} ≃
        {f : OriginalContinuousFramedFiber eS H σ //
          ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O S) (δ h)})
    (ESR : {f : S →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eS} ≃
        {f : OriginalContinuousFramedFiber eR H σ //
          ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O R) (δ h)})
    (ESS : {f : S →ₐ[O] S //
      (localCoefficientReduction eS).comp f = localCoefficientReduction eS} ≃
        {f : OriginalContinuousFramedFiber eS H σ //
          ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O S) (δ h)})
    (hRR : ∀ f x, (ERR f).val.val (π x) = GeneralLinearGroup.map f.val.toRingHom (τR x))
    (hRS : ∀ f x, (ERS f).val.val (π x) = GeneralLinearGroup.map f.val.toRingHom (τR x))
    (hSR : ∀ f x, (ESR f).val.val (π x) = GeneralLinearGroup.map f.val.toRingHom (τS x))
    (hSS : ∀ f x, (ESS f).val.val (π x) = GeneralLinearGroup.map f.val.toRingHom (τS x)) :
    (let e := framedCoefficientRingEquiv eR eS H π hπ σ δ τR τS ERR ERS ESR ESS hRR hRS hSR hSS
     (localCoefficientReduction eR).comp e.toAlgHom = localCoefficientReduction eS ∧
       ∀ x, GeneralLinearGroup.map e.toAlgHom.toRingHom (τS x) = τR x) := by
  let idR : {f : R →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eR} :=
    ⟨AlgHom.id O R, by ext; rfl⟩
  let f := ESR.symm (ERR idR)
  change (localCoefficientReduction eR).comp f.val = localCoefficientReduction eS ∧
    ∀ x, GeneralLinearGroup.map f.val.toRingHom (τS x) = τR x
  refine ⟨f.property, ?_⟩
  intro x
  calc
    _ = (ESR f).val.val (π x) := (hSR f x).symm
    _ = (ERR idR).val.val (π x) :=
      congrArg (fun z => z.val.val (π x)) (ESR.apply_symm_apply (ERR idR))
    _ = GeneralLinearGroup.map idR.val.toRingHom (τR x) := hRR idR x
    _ = τR x := by
      change GeneralLinearGroup.map (RingHom.id R) (τR x) = _
      rw [GeneralLinearGroup.map_id]
      rfl

end
end Dubon2026
