import Dubon2026.OriginalRelationKernelGroupEquiv
import Dubon2026.ArithmeticOriginalRelationClassTransport
import Dubon2026.ArithmeticOriginalStageClassColimitNaturality

/-! Transport the constructed original-stage class extension into the
actual arithmetic class colimit. The native class-colimit square already
preserves the original relation; only the canonical presentation maps for
the image-field isomorphism must be inverted. This is the remaining
extension input to DUB-17's proved finite S-unit correction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] relationTransportUnionAlgebra relationTransportStageAlgebra

private def stageImageRestrictionEquiv
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)
    (N : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    Gal(N.val/ℚ) ≃* Gal(originalUnramifiedStageInUnion a N / ℚ) := by
  let M := originalUnramifiedStageInUnion a N
  let e := originalUnramifiedStageInUnionEquiv a N
  letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
  letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
  letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
  let τ : Gal(N.val/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  have hτ : (τ : Gal(N.val/ℚ) → Gal(M/ℚ)) = e.autCongr := by
    funext σ
    apply AlgEquiv.ext
    intro x
    apply e.symm.injective
    change e.symm (τ σ x) = e.symm (e (σ (e.symm x)))
    rw [e.symm_apply_apply]
    exact σ.restrictNormal_commutes M x
  exact MulEquiv.ofBijective τ (hτ ▸ e.autCongr.bijective)

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
  (B : Rep.{0} ℤ Gal(originalUnramifiedStageInUnion a N / ℚ))
  (φ : originalRelationModule B ⟶
    arithmeticClassesModOutsideStageRep ℚ Ω a ha (originalUnramifiedStageInUnion a N))

/-- The exact image-stage relation-extension conclusion in the full-class colimit. -/
abbrev ArithmeticOriginalStageImageColimitExtensionResult : Prop :=
    let M := originalUnramifiedStageInUnion a N
    let e := originalUnramifiedStageInUnionEquiv a N
    let BN := arithmeticOriginalStageRestrictedCoefficient Ω a M N e.symm.toAlgHom B
    ∀ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ arithmeticOriginalStageClassRep Ω a ha N,
      originalRelationInclusion BN ≫ f =
        arithmeticOriginalStageRelationClassTransport Ω a ha M N e.symm.toAlgHom B φ →
      let πM : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(M/ℚ) :=
        AlgEquiv.restrictNormalHom M
      ∃ fG : Rep.res πM (Rep.free ℤ Gal(M/ℚ) B) ⟶ arithmeticClassesModOutsideColimitRep ℚ Ω a ha,
        (Rep.resFunctor πM).map (originalRelationInclusion B) ≫ fG =
          (Rep.resFunctor πM).map φ ≫ coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) M

/-- An extension at the original ambient stage yields an extension of
the same image-stage relation in the actual full-class colimit. -/
theorem arithmeticOriginalStageImage_extension_to_colimit :
    ArithmeticOriginalStageImageColimitExtensionResult Ω a ha N B φ := by
  unfold ArithmeticOriginalStageImageColimitExtensionResult
  intro M e BN f hf πM
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
  letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
  letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
  letI : Algebra N.val U :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a N)).toAlgebra
  letI : IsScalarTower ℚ N.val U :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a N))
  have hi (x : M) : (e.symm x : Ω) = (x.val : Ω) := by
    have h := originalUnramifiedStageInUnionEquiv_coe a N (e.symm x)
    rw [e.apply_symm_apply] at h
    exact h.symm
  letI : IsScalarTower M N.val U := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (hi x).symm)
  let πN : Gal(U/ℚ) →* Gal(N.val/ℚ) := AlgEquiv.restrictNormalHom N.val
  let τ : Gal(N.val/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  have hcomp : πM = τ.comp πN :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp ℚ M N.val U
  let g := stageImageRestrictionEquiv Ω a N
  let p := originalRelationFreeGroupChange τ B
  let r := originalRelationGroupChange τ B
  let pG : Rep.res πN (Rep.free ℤ Gal(N.val/ℚ) BN) ⟶ Rep.res πM (Rep.free ℤ Gal(M/ℚ) B) := by
    with_reducible_and_instances
      refine Rep.ofHom { toLinearMap := p.hom.toLinearMap, isIntertwining' := ?_ }
    intro σ
    with_reducible_and_instances apply LinearMap.ext
    intro x
    with_reducible_and_instances
      have hc : πM σ = τ (πN σ) := DFunLike.congr_fun hcomp σ
    have hequiv := Rep.hom_comm_apply p (πN σ) x
    with_reducible_and_instances
      exact hequiv.trans
        (congrArg (fun t : Gal(M/ℚ) => (Rep.free ℤ Gal(M/ℚ) B).ρ t (p.hom x)) hc.symm)
  let rG : Rep.res πN (originalRelationModule BN) ⟶ Rep.res πM (originalRelationModule B) := by
    with_reducible_and_instances
      refine Rep.ofHom { toLinearMap := r.hom.toLinearMap, isIntertwining' := ?_ }
    intro σ
    with_reducible_and_instances apply LinearMap.ext
    intro x
    with_reducible_and_instances
      have hc : πM σ = τ (πN σ) := DFunLike.congr_fun hcomp σ
    have hequiv := Rep.hom_comm_apply r (πN σ) x
    with_reducible_and_instances
      exact hequiv.trans
        (congrArg (fun t : Gal(M/ℚ) => (originalRelationModule B).ρ t (r.hom x)) hc.symm)
  have hp : Function.Bijective pG.hom := originalRelationFreeGroupChange_bijective g B
  have hr : Function.Surjective rG.hom := (originalRelationGroupChange_bijective g B).surjective
  let pIso : Rep.res πN (Rep.free ℤ Gal(N.val/ℚ) BN) ≅ Rep.res πM (Rep.free ℤ Gal(M/ℚ) B) :=
    Rep.mkIso (pG.hom.ofBijective hp)
  let fN := (Rep.resFunctor πN).map f ≫ arithmeticOriginalStageClassToColimit Ω a ha N
  refine ⟨pIso.inv ≫ fN, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  obtain ⟨s, hs⟩ := hr z
  have hinv : pIso.inv.hom (pG.hom ((originalRelationInclusion BN).hom s)) =
      (originalRelationInclusion BN).hom s :=
    congrArg (fun m => m.hom ((originalRelationInclusion BN).hom s)) pIso.hom_inv_id
  have hrel := congrArg (fun m => m.hom s) hf
  have hc := arithmeticOriginalStageClassToColimit_transition Ω a ha M N e.symm.toAlgHom hi
    (φ.hom (r.hom s))
  change fN.hom (pIso.inv.hom ((originalRelationInclusion B).hom z)) = _
  rw [← hs]
  exact (congrArg fN.hom hinv).trans
    ((congrArg (arithmeticOriginalStageClassToColimit Ω a ha N).hom hrel).trans hc)

end
end Dubon2026
