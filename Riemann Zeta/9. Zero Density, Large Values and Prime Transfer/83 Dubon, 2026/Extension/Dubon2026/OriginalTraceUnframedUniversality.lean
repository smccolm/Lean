import Dubon2026.OriginalPresentedTraceDescent
import Dubon2026.CompletedTraceCoefficientClassBijection

/-! # The actual original complete local trace ring represents the whole unframed deformation functor -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- The actual trace ring of the genuine original presentation is complete local and Noetherian, and one actual whole trace representation classifies every original continuous unframed lift over every complete local target by genuine continuous residue-preserving coefficient maps. All trace-ring properties and the universal representation are derived from the original residual representation. -/
theorem originalTraceUnframedUniversality_exists
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ.toMonoidHom))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation (originalPresentedResidualRestriction H q σ) H q hq)
    ∃ hlocal : IsLocalRing S,
      letI := hlocal
      IsNoetherianRing S ∧ IsAdic (IsLocalRing.maximalIdeal S) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
      ∃ (eS : IsLocalRing.ResidueField S ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι S)
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eS).toRingHom).comp
          τ.toMonoidHom = σ.toMonoidHom),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eS eA H
            σ.toMonoidHom τ hτres) := by
  let ρ := originalPresentedResidualRestriction H q σ
  let R := OriginalPresentedCoefficientRing H q σ
  letI : IsLocalRing R := originalPresentedCoefficientRing_isLocal H q σ
  have hR : IsAdic (IsLocalRing.maximalIdeal R) :=
    (originalPresentedCoefficientRing_localData H q σ).2.2.1
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  obtain ⟨hlocal, hnoeth, htop, hcomplete, _hretraction⟩ :=
    originalPresentedTraceAlgebra_localData (L := L) H q hq σ i₀
  letI : IsLocalRing S := hlocal
  letI : IsLocalHom S.val.toRingHom := originalAdicCoefficientSubalgebra_isLocalHom hR eR S
    (isClosed_closedMatrixTraceAlgebra υ)
  let eS := coefficientSubalgebraResidueEquiv eR S
  obtain ⟨τ, hτ, hτred⟩ := originalPresentedTraceDescent_exists (L := L) H q hq σ i₀
  have hτres : (GeneralLinearGroup.map (localCoefficientReduction eS).toRingHom).comp
      τ.toMonoidHom = σ.toMonoidHom := by
    rw [coefficientSubalgebraReduction_eq]
    exact hτred
  refine ⟨hlocal, hnoeth, htop, hcomplete, eS, τ, hτres, ?_⟩
  intro A _ _ _ _ _ hA eA
  exact completedTraceCoefficientClass_bijective hA ρ H q hq eA σ.toMonoidHom
    rfl τ hτ hτres

end
end Dubon2026
