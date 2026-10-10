import Dubon2026.OriginalPresentedTraceLocalData
import Dubon2026.MatrixStrictConjugacyCoefficientChange

/-! # Whole original trace descent from genuine absolute residual irreducibility -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Genuine original residual absolute irreducibility produces an actual whole continuous representation over the original trace ring, strictly conjugate to the original universal representation and reducing to the exact original whole residual representation. -/
theorem originalPresentedTraceDescent_exists
    (H : ProfiniteGrp.{0})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    (σ : H →ₜ* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ.toMonoidHom))] (i₀ : ι) :
    letI := originalPresentedCoefficientRing_isLocal H q σ
    let υ := completedPresentationRepresentation (originalPresentedResidualRestriction H q σ) H q hq
    let S := closedMatrixTraceAlgebra (O := O) υ
    let eR := completedPresentationResidueEquiv
      (originalPresentedResidualRestriction H q σ) q.toMonoidHom.ker
    ∃ τ : H →ₜ* GeneralLinearGroup ι S,
      MatrixStrictlyConjugate (IsLocalRing.residue (OriginalPresentedCoefficientRing H q σ))
        ((GeneralLinearGroup.map S.val.toRingHom).comp τ.toMonoidHom) υ ∧
      (GeneralLinearGroup.map ((localCoefficientReduction eR).comp S.val).toRingHom).comp
        τ.toMonoidHom = σ.toMonoidHom := by
  let ρ := originalPresentedResidualRestriction H q σ
  let R := OriginalPresentedCoefficientRing H q σ
  letI : IsLocalRing R := originalPresentedCoefficientRing_isLocal H q σ
  have hdata := originalPresentedCoefficientRing_localData H q σ
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hdata.2.1
  have hR : IsAdic (IsLocalRing.maximalIdeal R) := hdata.2.2.1
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  letI : Algebra (IsLocalRing.ResidueField R) L :=
    ((algebraMap (IsLocalRing.ResidueField O) L).comp eR.toRingHom).toAlgebra
  have hext := trueResidueScalarExtension_eq (L := L) eR
    (completedPresentationRepresentation ρ H q hq) σ.toMonoidHom
    (originalPresentedCoefficientRing_universal_residue H q hq σ)
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp
          (completedPresentationRepresentation ρ H q hq)))) := by
    rw [hext]
    infer_instance
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let υc : H →ₜ* GeneralLinearGroup ι R :=
    ⟨υ, completedPresentedGroupRepresentation_continuous ρ H q hq⟩
  obtain ⟨τ, hτ⟩ := originalAdicContinuousTraceRepresentationDescent_exists
    (L := L) hR eR υc i₀
  refine ⟨τ, hτ, ?_⟩
  have hred := matrixStrictlyConjugate_reduction (localCoefficientReduction eR).toRingHom
    ((GeneralLinearGroup.map S.val.toRingHom).comp τ.toMonoidHom) υ
    (matrixStrictlyConjugate_comp_reduction (IsLocalRing.residue R) eR.toRingHom _ _ hτ)
  exact hred.symm.trans (originalPresentedCoefficientRing_universal_residue H q hq σ)

end
end Dubon2026
