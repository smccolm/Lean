import Dubon2026.CompletedPresentationConjugatingEndomorphism
import Dubon2026.CompletedPresentationSubalgebraImage
import Dubon2026.OriginalAdicTraceRepresentationDescent
import Dubon2026.OriginalAdicCoefficientSubalgebraLocality
import Dubon2026.OriginalTraceEndomorphismRetraction

/-! # A genuine continuous retraction onto the actual original universal trace coefficient ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The actual universal trace coefficient ring is a continuous retract of its original completed presentation ring: genuine whole trace descent, original framed universality, actual coefficient-image density and trace equality construct the retraction. -/
theorem completedPresentationTraceAlgebra_retraction_exists
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue
          (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))).comp
          (completedPresentationRepresentation ρ H q hq))))] (i₀ : ι) :
    ∃ f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O]
        closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq),
      (∀ x : closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq),
        f x = x) ∧ Continuous f := by
  let R := CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  letI : T2Space R := (IsAdic.isHausdorff_iff hR).mp inferInstance
  let υc : H →ₜ* GeneralLinearGroup ι R :=
    ⟨υ, completedPresentedGroupRepresentation_continuous ρ H q hq⟩
  obtain ⟨τ, hτ⟩ := originalAdicContinuousTraceRepresentationDescent_exists
    (L := L) hR eR υc i₀
  have hinc : Continuous (GeneralLinearGroup.map (n := ι) S.val.toRingHom) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact continuous_subtype_val.comp (continuous_apply_apply i j)
  let τR : H →ₜ* GeneralLinearGroup ι R :=
    ⟨(GeneralLinearGroup.map S.val.toRingHom).comp τ.toMonoidHom, hinc.comp τ.continuous⟩
  obtain ⟨φ, hφ, hcφ⟩ := completedPresentation_conjugating_endomorphism_exists
    ρ H q hq hR τR hτ
  have heq : (GeneralLinearGroup.map φ.toRingHom).comp υ = τR.toMonoidHom :=
    MonoidHom.ext hφ
  have hconj : MatrixStrictlyConjugate (IsLocalRing.residue R)
      ((GeneralLinearGroup.map φ.toRingHom).comp υ) υ := by
    rw [heq]
    exact hτ
  have hS : IsClosed (S : Set R) := isClosed_closedMatrixTraceAlgebra υ
  have himage : ∀ x : R, φ x ∈ S := by
    apply completedPresentation_image_mem_subalgebra ρ H q hq S hS
      (originalAdicCoefficientSubalgebra_isUnit hR eR S hS) φ hcφ
    intro h i j
    have he := congrArg (fun U : GeneralLinearGroup ι R => U.val i j) (hφ h)
    change φ ((υ h).val i j) = ((τ h).val i j : R) at he
    rw [he]
    exact ((τ h).val i j).property
  refine ⟨φ.codRestrict S himage, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact originalTraceEndomorphism_fixes_trace_algebra (IsLocalRing.residue R) υ φ hcφ hconj x
  · exact hcφ.subtype_mk himage

/-- The actual original universal trace coefficient ring is Noetherian because the constructed original retraction makes it a quotient of the same proved Noetherian presentation ring. -/
theorem completedPresentationTraceAlgebra_isNoetherian
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsAdicComplete (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal
      (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue
          (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))).comp
          (completedPresentationRepresentation ρ H q hq))))] (i₀ : ι) :
    IsNoetherianRing (closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation ρ H q hq)) := by
  obtain ⟨f, hfix, _hc⟩ := completedPresentationTraceAlgebra_retraction_exists
    (L := L) ρ H q hq hR i₀
  letI := completedPresentationCoefficientQuotient_isNoetherian ρ q.toMonoidHom.ker
  apply isNoetherianRing_of_surjective _ _ f.toRingHom
  intro x
  exact ⟨x.val, hfix x⟩

end
end Dubon2026
