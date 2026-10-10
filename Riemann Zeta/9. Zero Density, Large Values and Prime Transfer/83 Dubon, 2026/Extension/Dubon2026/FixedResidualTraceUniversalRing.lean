import Dubon2026.FixedResidualFramedUniversality
import Dubon2026.OriginalPresentedTraceLocalData
import Dubon2026.FixedResidualAbsoluteIrreducibility
import Dubon2026.MatrixStrictConjugacySurjectiveRestriction

/-! # The actual whole-group trace ring of the original fixed-residual presentation -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- The actual original whole-group universal trace algebra is exactly the same closed subalgebra as the genuine fixed-residual quotient trace algebra, because the original quotient map is surjective. -/
theorem fixedResidualTraceAlgebra_eq
    (p : ℕ) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) :
    closedMatrixTraceAlgebra (O := O) (fixedResidualFramedUniversalRepresentation p H σ hσ S hS) =
      closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation
        (originalPresentedResidualRestriction (originalResidualProfiniteGroup p H σ hσ)
          (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
          (fixedResidualOriginalRepresentation p H σ hσ))
        (originalResidualProfiniteGroup p H σ hσ)
        (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S) hS) := by
  let N := fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)
  exact closedMatrixTraceAlgebra_comp_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) _

/-- Original residual absolute irreducibility derives the actual complete local Noetherian trace ring of the whole original universal representation, with its own maximal-adic topology and actual continuous retraction. -/
theorem fixedResidualTraceAlgebra_localData
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]
    (p : ℕ) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) (i₀ : ι) :
    let T := closedMatrixTraceAlgebra (O := O)
      (fixedResidualFramedUniversalRepresentation p H σ hσ S hS)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ f : FixedResidualFramedCoefficientRing p H σ hσ S →ₐ[O] T,
        (∀ x : T, f x = x) ∧ Continuous f := by
  letI := fixedResidualOriginalRepresentation_absoluteIrreducible (L := L) p H σ hσ
  rw [fixedResidualTraceAlgebra_eq p H σ hσ S hS]
  exact originalPresentedTraceAlgebra_localData (L := L)
    (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S) hS
    (fixedResidualOriginalRepresentation p H σ hσ) i₀

end
end Dubon2026
