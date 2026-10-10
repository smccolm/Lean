import Dubon2026.CompletedPresentationConjugatingEndomorphism
import Dubon2026.CompletedPresentationSubalgebraImage
import Dubon2026.OriginalAdicTraceRepresentationDescent
import Dubon2026.OriginalAdicCoefficientSubalgebraLocality
import Dubon2026.OriginalTraceEndomorphismRetraction
import Dubon2026.CompletedPresentationTraceRetraction
import Dubon2026.OriginalAdicCoefficientRetractionCompleteness

/-! # Complete local data for the actual original universal trace coefficient ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The same actual original universal trace ring has proved locality, Noetherianity, its own maximal-adic topology and completeness, together with the constructed original continuous retraction. -/
theorem completedPresentationTraceAlgebra_localData
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
    let S := closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)
    letI : IsLocalRing S := originalAdicCoefficientSubalgebra_isLocalRing hR
      (completedPresentationResidueEquiv ρ q.toMonoidHom.ker) S
      (isClosed_closedMatrixTraceAlgebra (completedPresentationRepresentation ρ H q hq))
    IsNoetherianRing S ∧ IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ f : CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker →ₐ[O] S,
        (∀ x : S, f x = x) ∧ Continuous f := by
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  have hS : IsClosed (S : Set (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)) :=
    isClosed_closedMatrixTraceAlgebra υ
  letI : IsLocalRing S := originalAdicCoefficientSubalgebra_isLocalRing hR eR S hS
  letI : IsLocalHom S.val.toRingHom := originalAdicCoefficientSubalgebra_isLocalHom hR eR S hS
  obtain ⟨f, hfix, hcf⟩ := completedPresentationTraceAlgebra_retraction_exists
    (L := L) ρ H q hq hR i₀
  have htop := originalAdicCoefficientRetraction_localTopology hR S hS f hfix
  have hnoeth := completedPresentationTraceAlgebra_isNoetherian (L := L) ρ H q hq hR i₀
  exact ⟨hnoeth, htop.1, htop.2, f, hfix, hcf⟩

end
end Dubon2026
