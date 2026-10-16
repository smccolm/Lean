import Dubon2026.LocalFieldOriginalUnramifiedInvariant
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # The normalized local invariant under the actual closure embedding

Use the proved unramified representative of the original class. The same
finite field and same class compute both full invariants by the original
period formula. This discharges closure-choice transport for DUB-17's
canonical arithmetic prime-coordinate comparison.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- Actual coefficient extension between separably closed Galois fields preserves the normalized local invariant. -/
theorem localFieldContinuousInvariant_closure_transport
    (K Ω Ξ : Type) [Field K] [Field Ω] [Field Ξ]
    [Algebra K Ω] [Algebra K Ξ] [Algebra Ω Ξ] [IsScalarTower K Ω Ξ]
    [IsGalois K Ω] [IsGalois K Ξ] [IsSepClosed Ω] [IsSepClosed Ξ]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ξ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ξ)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    localFieldContinuousH2InvariantEquiv K Ξ (continuousGaloisUnitBaseChangeH2 K K Ω Ξ x) =
      localFieldContinuousH2InvariantEquiv K Ω x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨F, hF, y, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  letI : Algebra F Ξ := ((algebraMap Ω Ξ).comp (algebraMap F Ω)).toAlgebra
  letI : SMul F Ω := (inferInstance : Algebra F Ω).toSMul
  letI : SMul F Ξ := (inferInstance : Algebra F Ξ).toSMul
  letI : IsScalarTower F Ω Ξ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F Ξ := IsScalarTower.of_algebraMap_eq' (by
    ext k
    exact IsScalarTower.algebraMap_apply K Ω Ξ k)
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  have hs := continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F y
  have hc := (congrArg (continuousGaloisUnitBaseChangeH2 K K Ω Ξ) hs.symm).trans
    (continuousGaloisUnitBaseChangeH2_comp K K K F Ω Ξ y)
  exact (congrArg (localFieldContinuousH2InvariantEquiv K Ξ) hc).trans
    ((localFieldOriginalUnramified_invariant K F Ξ y).trans
      ((localFieldOriginalUnramified_invariant K F Ω y).symm.trans
        (congrArg (localFieldContinuousH2InvariantEquiv K Ω) hs)))

end
end Dubon2026
