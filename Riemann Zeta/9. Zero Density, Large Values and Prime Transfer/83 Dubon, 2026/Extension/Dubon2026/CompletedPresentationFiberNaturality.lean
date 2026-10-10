import Dubon2026.CompletedPresentationFramedFibers

/-! # Naturality of the actual continuous framed fibers under original coefficient maps -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A B : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Postcomposition by the actual original continuous residue-preserving coefficient map. -/
def presentedCoefficientFiberPostcomp
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : PresentedContinuousCoefficientFiber ρ eA H q) :
    PresentedContinuousCoefficientFiber ρ eB H q := by
  refine ⟨k.comp f.val, hk.comp f.property.1, ?_⟩
  rw [← AlgHom.comp_assoc, hres]
  exact f.property.2

/-- Change every matrix of the original whole continuous representation using the original coefficient map. -/
def presentedRepresentationFiberPostcomp
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (σ : PresentedContinuousRepresentationFiber ρ eA H q) :
    PresentedContinuousRepresentationFiber ρ eB H q := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) k.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact hk.comp (continuous_apply_apply i j)
  let τ : H →ₜ* GeneralLinearGroup ι B :=
    ⟨(GeneralLinearGroup.map (n := ι) k.toRingHom).comp σ.val.toMonoidHom,
      hmap.comp σ.val.continuous⟩
  refine ⟨τ, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hc := DFunLike.congr_fun hres
    ((σ.val (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))).val i j)
  have hs := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun σ.property g)
  exact hc.trans hs

/-- The actual continuous framed-fiber equivalence commutes with every genuine original continuous residue-preserving coefficient map. -/
theorem completedPresentationFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : PresentedContinuousCoefficientFiber ρ eA H q) :
    completedPresentationFramedFiberEquiv hB ρ eB H q hq
      (presentedCoefficientFiberPostcomp ρ eA eB H q k hk hres f) =
        presentedRepresentationFiberPostcomp ρ eA eB H q k hk hres
          (completedPresentationFramedFiberEquiv hA ρ eA H q hq f) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro h
  rfl

end
end Dubon2026
