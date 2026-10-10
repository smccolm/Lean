import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.LocalCoefficientReductionTopology
import Dubon2026.CompletedPresentationFramedFibers

/-! # The whole original framed fiber of a genuine profinite presentation -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

omit [Group.FG G] [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- The actual residual condition on the original dense abstract group is equivalent to the exact residual condition on the whole original profinite target. -/
theorem presentedFramedResidual_iff_whole
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : H →ₜ* GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction (f.comp q)) =
        (σ.toMonoidHom.comp q.toMonoidHom).comp
          (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom ↔
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      f.toMonoidHom = σ.toMonoidHom := by
  constructor
  · intro hf
    have hmap : Continuous (GeneralLinearGroup.map (n := ι)
        (localCoefficientReduction e).toRingHom) := by
      apply Units.continuous_map
      apply continuous_matrix
      intro i j
      exact (localCoefficientReduction_continuous hA e).comp (continuous_apply_apply i j)
    have he := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
      (hmap.comp (f.comp q).continuous) (σ.comp q).continuous
      (funext fun g => DFunLike.congr_fun hf g)
    apply MonoidHom.ext
    intro h
    obtain ⟨x, rfl⟩ := hq h
    exact congrFun he x
  · intro hf
    apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun hf (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))

/-- The actual presented continuous fiber retains exactly the entire original framed fiber with its original residual representation. -/
def presentedWholeFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    PresentedContinuousRepresentationFiber
      ((σ.toMonoidHom.comp q.toMonoidHom).comp
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) e H q ≃
      OriginalContinuousFramedFiber e H σ.toMonoidHom where
  toFun f := ⟨f.val, (presentedFramedResidual_iff_whole hA e H q hq σ f.val).mp f.property⟩
  invFun f := ⟨f.val, (presentedFramedResidual_iff_whole hA e H q hq σ f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original all-relation completed coefficient quotient classifies the whole original framed representation fiber. -/
def completedPresentationWholeFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    PresentedContinuousCoefficientFiber
      ((σ.toMonoidHom.comp q.toMonoidHom).comp
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) e H q ≃
      OriginalContinuousFramedFiber e H σ.toMonoidHom :=
  (completedPresentationFramedFiberEquiv hA _ e H q hq).trans
    (presentedWholeFramedFiberEquiv hA e H q hq σ)

/-- The whole-fiber equivalence uses the actual original universal matrices. -/
theorem completedPresentationWholeFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : PresentedContinuousCoefficientFiber
      ((σ.toMonoidHom.comp q.toMonoidHom).comp
        (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) e H q) (h : H) :
    (completedPresentationWholeFramedFiberEquiv hA e H q hq σ f).val h =
      GeneralLinearGroup.map (n := ι) f.val.toRingHom
        (completedPresentationRepresentation
          ((σ.toMonoidHom.comp q.toMonoidHom).comp
            (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom) H q hq h) := rfl

end
end Dubon2026
