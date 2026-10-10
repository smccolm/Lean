import Dubon2026.OriginalPresentedCoefficientRing
import Dubon2026.CompletedPresentationTraceLocalData
import Dubon2026.TrueResidueScalarExtension

/-! # Complete local trace coefficients from the original whole residual representation -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- Original absolute residual irreducibility and the genuine profinite presentation derive the complete local trace ring and its actual continuous retraction; no presentation-ring local data or trace-ring property is assumed. -/
theorem originalPresentedTraceAlgebra_localData
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
        ∃ f : OriginalPresentedCoefficientRing H q σ →ₐ[O] S,
          (∀ x : S, f x = x) ∧ Continuous f := by
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
  let S := closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)
  let hlocal : IsLocalRing S := originalAdicCoefficientSubalgebra_isLocalRing hR eR S
    (isClosed_closedMatrixTraceAlgebra (completedPresentationRepresentation ρ H q hq))
  exact ⟨hlocal, completedPresentationTraceAlgebra_localData (L := L) ρ H q hq hR i₀⟩

end
end Dubon2026
