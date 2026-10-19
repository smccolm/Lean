import Dubon2026.OriginalCoefficientFramedEquivalence

/-! Matrix rigidity extracted from the already proved framed
classification. Applied to each actual universal ring, this discharges
the endomorphism hypotheses of the two-map ring comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- A classified coefficient endomorphism fixing all actual universal
matrices is the identity. Surjective arithmetic restriction suffices
to test those matrices on the auxiliary-support group. -/
theorem framedCoefficient_endomorphism_eq_id
    {ι O R : Type u} {G : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [WithIdeal R]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (H : ProfiniteGrp.{u}) (π : G → H) (hπ : Function.Surjective π)
    (σ : H →* GeneralLinearGroup ι (ResidueField O)) (δ : H →* Oˣ)
    (τ : G → GeneralLinearGroup ι R)
    (E : {f : R →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eR} ≃
        {f : OriginalContinuousFramedFiber eR H σ //
          ∀ h, GeneralLinearGroup.det (f.val h) = Units.map (algebraMap O R) (δ h)})
    (heval : ∀ f x, (E f).val.val (π x) = GeneralLinearGroup.map f.val.toRingHom (τ x))
    (f : R →ₐ[O] R)
    (hres : (localCoefficientReduction eR).comp f = localCoefficientReduction eR)
    (hf : ∀ x, GeneralLinearGroup.map f.toRingHom (τ x) = τ x) : f = AlgHom.id O R := by
  let idR : {f : R →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eR} :=
    ⟨AlgHom.id O R, by ext; rfl⟩
  have he : E ⟨f, hres⟩ = E idR := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro h
    obtain ⟨x, rfl⟩ := hπ h
    rw [heval, heval, hf]
    change τ x = GeneralLinearGroup.map (RingHom.id R) (τ x)
    rw [GeneralLinearGroup.map_id]
    rfl
  exact congrArg Subtype.val (E.injective he)

end
end Dubon2026
