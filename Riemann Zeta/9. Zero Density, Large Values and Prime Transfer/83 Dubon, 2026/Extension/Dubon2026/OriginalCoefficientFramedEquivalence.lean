import Dubon2026.OriginalPresentedCoefficientRing

/-! # Actual residue-preserving coefficient maps classify original framed representations -/

namespace Dubon2026

noncomputable section
open Matrix

/-- The genuine continuous maps of original local coefficient algebras inducing the specified identity of residue fields. -/
abbrev OriginalContinuousCoefficientFiber
    {O R A : Type*} [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
    [CommRing A] [IsLocalRing A] [Algebra O A] [TopologicalSpace A]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :=
  {f : R →ₐ[O] A // Continuous f ∧
    (localCoefficientReduction eA).comp f = localCoefficientReduction eR}

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

omit [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- The actual full residue-preserving condition is equivalent to its genuine original completed-coordinate restriction, using surjectivity of the original relation quotient. -/
theorem originalPresentedCoefficient_residue_iff
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (f : OriginalPresentedCoefficientRing H q σ →ₐ[O] A) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     (localCoefficientReduction eA).comp f =
       localCoefficientReduction (completedPresentationResidueEquiv
         (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) ↔
     ((localCoefficientReduction eA).comp f).comp
       (Ideal.Quotient.mkₐ O (completedPresentationRelationIdeal
         (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker)) =
           completedResidualRepresentationEvaluation (originalPresentedResidualRestriction H q σ)) := by
  let ρ := originalPresentedResidualRestriction H q σ
  letI := originalPresentedCoefficientRing_isLocal H q σ
  let J := completedPresentationRelationIdeal ρ q.toMonoidHom.ker
  constructor
  · intro hf
    apply AlgHom.ext
    intro r
    exact (DFunLike.congr_fun hf (Ideal.Quotient.mk J r)).trans
      (completedPresentationResidueEquiv_original ρ q.toMonoidHom.ker r)
  · intro hf
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun hf r).trans
      (completedPresentationResidueEquiv_original ρ q.toMonoidHom.ker r).symm

/-- Genuine continuous residue-preserving maps from the actual local coefficient ring are exactly its previously constructed original coefficient fiber. -/
def originalPresentedCoefficientFiberEquiv
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA ≃
       PresentedContinuousCoefficientFiber (originalPresentedResidualRestriction H q σ) eA H q) := by
  letI := originalPresentedCoefficientRing_isLocal H q σ
  exact {
    toFun := fun f => ⟨f.val, f.property.1,
      (originalPresentedCoefficient_residue_iff eA H q σ f.val).mp f.property.2⟩
    invFun := fun f => ⟨f.val, f.property.1,
      (originalPresentedCoefficient_residue_iff eA H q σ f.val).mpr f.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The actual complete local presentation ring represents the entire original continuous framed fiber by genuine residue-preserving coefficient maps. -/
def originalPresentedFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA ≃
       OriginalContinuousFramedFiber eA H σ.toMonoidHom) :=
  (originalPresentedCoefficientFiberEquiv eA H q σ).trans
    (completedPresentationWholeFramedFiberEquiv hA eA H q hq σ)

/-- The actual coefficient-to-framed equivalence is evaluation of every original universal matrix. -/
theorem originalPresentedFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    (letI := originalPresentedCoefficientRing_isLocal H q σ
     ∀ (f : OriginalContinuousCoefficientFiber (completedPresentationResidueEquiv
       (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker) eA) (h : H),
       (originalPresentedFramedFiberEquiv hA eA H q hq σ f).val h =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (completedPresentationRepresentation
             (originalPresentedResidualRestriction H q σ) H q hq h)) := by
  dsimp only
  intro f h
  rfl

end
end Dubon2026
