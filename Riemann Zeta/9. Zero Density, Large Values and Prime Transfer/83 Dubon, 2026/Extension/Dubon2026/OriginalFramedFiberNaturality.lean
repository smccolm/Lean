import Dubon2026.OriginalCoefficientFramedEquivalence

/-! # Naturality on actual coefficient maps and whole original framed lifts -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
section Coefficient
variable {O R A B : Type u} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [TopologicalSpace B]

/-- Postcompose genuine continuous residue-preserving coefficient maps with an original coefficient morphism. -/
def originalCoefficientFiberPostcomp
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : OriginalContinuousCoefficientFiber eR eA) :
    OriginalContinuousCoefficientFiber eR eB := by
  refine ⟨k.comp f.val, hk.comp f.property.1, ?_⟩
  rw [← AlgHom.comp_assoc, hres]
  exact f.property.2

end Coefficient

variable {O A B : Type u} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

section Framed
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [WithIdeal A] [WithIdeal B]

/-- Apply an actual original continuous coefficient morphism to every whole matrix of an original framed lift. -/
def originalFramedFiberPostcomp
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (f : OriginalContinuousFramedFiber eA H σ) :
    OriginalContinuousFramedFiber eB H σ := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) k.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact hk.comp (continuous_apply_apply i j)
  refine ⟨⟨(GeneralLinearGroup.map (n := ι) k.toRingHom).comp f.val.toMonoidHom,
    hmap.comp f.val.continuous⟩, ?_⟩
  apply MonoidHom.ext
  intro h
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hc := DFunLike.congr_fun hres ((f.val h).val i j)
  have hf := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun f.property h)
  exact hc.trans hf

end Framed

section Presented
variable {G ι : Type u} [Group G] [Group.FG G] [Fintype ι] [DecidableEq ι]
  [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [WithIdeal A] [WithIdeal B]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The actual coefficient-map classification commutes with every original continuous residue-preserving coefficient morphism. This is the literal naturality identity of original universal-matrix evaluation. -/
theorem originalPresentedFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     ∀ f : OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA,
       originalPresentedFramedFiberEquiv hB eB H q hq σ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB H σ.toMonoidHom k hk hres
             (originalPresentedFramedFiberEquiv hA eA H q hq σ f)) := by
  dsimp only
  intro f
  apply Subtype.ext
  apply DFunLike.ext
  intro h
  rfl

end Presented
end
end Dubon2026
