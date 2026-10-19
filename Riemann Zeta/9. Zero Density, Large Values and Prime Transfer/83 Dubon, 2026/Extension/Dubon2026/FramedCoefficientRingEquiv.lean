import Dubon2026.ResidueMatrixCoefficientEquiv
import Dubon2026.FramedCoefficientMatrixRigidity

/-! The concrete isomorphism constructed from two actual framed
classifications. Only evaluation at the two representing coefficient
rings is needed. This avoids a separate general representability theory
in the original-support quotient comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
universe u

/-- Two rings whose actual coefficient fibers classify the same framed
lifts, with the specified universal-matrix evaluation, are isomorphic
over the original coefficient ring. The maps are constructed from the
two identity coefficient points and proved inverse by matrix rigidity. -/
def framedCoefficientRingEquiv
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
    S ≃ₐ[O] R := by
  let idR : {f : R →ₐ[O] R //
      (localCoefficientReduction eR).comp f = localCoefficientReduction eR} :=
    ⟨AlgHom.id O R, by ext; rfl⟩
  let idS : {f : S →ₐ[O] S //
      (localCoefficientReduction eS).comp f = localCoefficientReduction eS} :=
    ⟨AlgHom.id O S, by ext; rfl⟩
  let f := ESR.symm (ERR idR)
  let g := ERS.symm (ESS idS)
  have hf : ∀ x, GeneralLinearGroup.map f.val.toRingHom (τS x) = τR x := by
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
  have hg : ∀ x, GeneralLinearGroup.map g.val.toRingHom (τR x) = τS x := by
    intro x
    calc
      _ = (ERS g).val.val (π x) := (hRS g x).symm
      _ = (ESS idS).val.val (π x) :=
        congrArg (fun z => z.val.val (π x)) (ERS.apply_symm_apply (ESS idS))
      _ = GeneralLinearGroup.map idS.val.toRingHom (τS x) := hSS idS x
      _ = τS x := by
        change GeneralLinearGroup.map (RingHom.id S) (τS x) = _
        rw [GeneralLinearGroup.map_id]
        rfl
  exact residueMatrixCoefficientEquiv eR eS τR τS f.val g.val f.property g.property hf hg
    (framedCoefficient_endomorphism_eq_id eR H π hπ σ δ τR ERR hRR)
    (framedCoefficient_endomorphism_eq_id eS H π hπ σ δ τS ESS hSS)

end
end Dubon2026
