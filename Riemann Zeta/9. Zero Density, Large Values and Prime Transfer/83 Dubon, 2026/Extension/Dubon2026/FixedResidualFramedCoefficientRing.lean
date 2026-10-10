import Dubon2026.OriginalFramedFiberNaturality
import Dubon2026.ProfiniteGeneratorPresentations

/-! # The genuine complete local ring attached to the original fixed residual quotient -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {ι O : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]

/-- The same genuine profinite quotient determined solely by the original residual representation. -/
abbrev originalResidualProfiniteGroup (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ) :=
  fixedResidualProfiniteQuotient p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)

/-- The actual complete local all-relation ring obtained from original generators of the fixed residual quotient. -/
abbrev FixedResidualFramedCoefficientRing (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ)) :=
  OriginalPresentedCoefficientRing (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
    (fixedResidualOriginalRepresentation p H σ hσ)

/-- Locality of the original fixed-residual coefficient ring is derived from the actual original residual relations. -/
theorem fixedResidualFramedCoefficientRing_isLocal
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ)) :
    IsLocalRing (FixedResidualFramedCoefficientRing p H σ hσ S) :=
  originalPresentedCoefficientRing_isLocal (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
    (fixedResidualOriginalRepresentation p H σ hσ)

/-- The original fixed-residual coefficient ring has its actual original residue-field identification. -/
def fixedResidualFramedCoefficientResidueEquiv
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     IsLocalRing.ResidueField (FixedResidualFramedCoefficientRing p H σ hσ S) ≃ₐ[O]
       IsLocalRing.ResidueField O) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
  exact completedPresentationResidueEquiv
    (originalPresentedResidualRestriction (originalResidualProfiniteGroup p H σ hσ)
      (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
      (fixedResidualOriginalRepresentation p H σ hσ))
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S).toMonoidHom.ker

/-- The actual original fixed-residual ring is Noetherian and maximally adically complete, and its literal topology is that maximal-adic topology. -/
theorem fixedResidualFramedCoefficientRing_localData
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (S : Finset (originalResidualProfiniteGroup p H σ hσ)) :
    (letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
     IsNoetherianRing (FixedResidualFramedCoefficientRing p H σ hσ S) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FixedResidualFramedCoefficientRing p H σ hσ S))
         (FixedResidualFramedCoefficientRing p H σ hσ S) ∧
       (inferInstance : TopologicalSpace (FixedResidualFramedCoefficientRing p H σ hσ S)) =
         (IsLocalRing.maximalIdeal (FixedResidualFramedCoefficientRing p H σ hσ S)).adicTopology) := by
  letI := fixedResidualFramedCoefficientRing_isLocal p H σ hσ S
  have hd := originalPresentedCoefficientRing_localData (originalResidualProfiniteGroup p H σ hσ)
    (profiniteGeneratorPresentation (originalResidualProfiniteGroup p H σ hσ) S)
    (fixedResidualOriginalRepresentation p H σ hσ)
  exact ⟨hd.1, hd.2.1, hd.2.2.1⟩

end
end Dubon2026
