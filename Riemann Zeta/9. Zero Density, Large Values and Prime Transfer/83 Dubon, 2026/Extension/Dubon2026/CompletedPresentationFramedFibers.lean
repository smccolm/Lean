import Dubon2026.CompletedPresentationUniversality

/-! # The actual continuous framed fibers of the original completed presentation -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- The genuine continuous residue-preserving coefficient maps out of the actual original relation quotient. -/
abbrev PresentedContinuousCoefficientFiber
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H) :=
  {f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] A //
    Continuous f ∧ ((localCoefficientReduction e).comp f).comp
      (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal ρ q.toMonoidHom.ker)) =
        completedResidualRepresentationEvaluation ρ}

/-- The whole original continuous matrix representations with the exact original residual restriction. -/
abbrev PresentedContinuousRepresentationFiber
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H) :=
  {σ : H →ₜ* GeneralLinearGroup ι A //
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      (profiniteMatrixRestriction (σ.comp q)) = ρ}

/-- Evaluate the original universal matrices using an actual continuous coefficient map. -/
def presentedRepresentationFromCoefficients
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (f : PresentedContinuousCoefficientFiber ρ e H q) :
    PresentedContinuousRepresentationFiber ρ e H q := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) f.val.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact f.property.1.comp (continuous_apply_apply i j)
  let σ : H →ₜ* GeneralLinearGroup ι A :=
    ⟨(GeneralLinearGroup.map (n := ι) f.val.toRingHom).comp
      (completedPresentationRepresentation ρ H q hq),
      hmap.comp (completedPresentedGroupRepresentation_continuous ρ H q hq)⟩
  refine ⟨σ, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change localCoefficientReduction e (f.val
    ((completedPresentationRepresentation ρ H q hq
      (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))).val i j)) =
        (ρ g).val i j
  rw [completedPresentationRepresentation_original, completedUniversalProfiniteRepresentation_eta]
  have hf := DFunLike.congr_fun f.property.2
    ((completedUniversalMatrixRepresentation ρ g).val i j)
  have hr := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun (completedUniversalMatrixRepresentation_reduction ρ) g)
  exact hf.trans hr

/-- The proved unique coefficient map associated to the whole original continuous representation. -/
def presentedCoefficientsFromRepresentation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (σ : PresentedContinuousRepresentationFiber ρ e H q) :
    PresentedContinuousCoefficientFiber ρ e H q :=
  ⟨Classical.choose (completedPresentationCoefficient_exists_unique
    hA ρ e H q hq σ.val σ.property),
    (Classical.choose_spec (completedPresentationCoefficient_exists_unique
      hA ρ e H q hq σ.val σ.property)).1.2⟩

/-- The actual coefficient reconstruction recovers every matrix of the original entire continuous representation. -/
theorem presentedRepresentation_coefficients_inverse
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (σ : PresentedContinuousRepresentationFiber ρ e H q) :
    presentedRepresentationFromCoefficients ρ e H q hq
      (presentedCoefficientsFromRepresentation hA ρ e H q hq σ) = σ := by
  apply Subtype.ext
  apply DFunLike.ext
  intro h
  exact (Classical.choose_spec (completedPresentationCoefficient_exists_unique
    hA ρ e H q hq σ.val σ.property)).1.1 h

/-- The whole original matrix representation determines every original coefficient of its actual continuous coefficient map. -/
theorem presentedCoefficients_representation_inverse
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (f : PresentedContinuousCoefficientFiber ρ e H q) :
    presentedCoefficientsFromRepresentation hA ρ e H q hq
      (presentedRepresentationFromCoefficients ρ e H q hq f) = f := by
  apply Subtype.ext
  let σ := presentedRepresentationFromCoefficients ρ e H q hq f
  exact ((Classical.choose_spec (completedPresentationCoefficient_exists_unique
    hA ρ e H q hq σ.val σ.property)).2 f.val ⟨fun _ => rfl, f.property⟩).symm

/-- The actual continuous framed coefficient fiber is equivalent to the entire original continuous matrix-representation fiber. -/
def completedPresentationFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) :
    PresentedContinuousCoefficientFiber ρ e H q ≃
      PresentedContinuousRepresentationFiber ρ e H q where
  toFun := presentedRepresentationFromCoefficients ρ e H q hq
  invFun := presentedCoefficientsFromRepresentation hA ρ e H q hq
  left_inv := presentedCoefficients_representation_inverse hA ρ e H q hq
  right_inv := presentedRepresentation_coefficients_inverse hA ρ e H q hq

/-- The genuine framed-fiber equivalence evaluates every original universal matrix at the original group element. -/
theorem completedPresentationFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) (f : PresentedContinuousCoefficientFiber ρ e H q) (h : H) :
    (completedPresentationFramedFiberEquiv hA ρ e H q hq f).val h =
      GeneralLinearGroup.map (n := ι) f.val.toRingHom
        (completedPresentationRepresentation ρ H q hq h) := rfl

/-- The actual original coefficient-evaluation map is bijective on the full continuous framed fibers. -/
theorem completedPresentationFramedFiberEquiv_bijective
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q) :
    Function.Bijective (completedPresentationFramedFiberEquiv hA ρ e H q hq) :=
  (completedPresentationFramedFiberEquiv hA ρ e H q hq).bijective

end
end Dubon2026
