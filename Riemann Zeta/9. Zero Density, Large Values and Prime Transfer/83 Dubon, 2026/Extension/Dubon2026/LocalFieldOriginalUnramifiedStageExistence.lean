import Dubon2026.LocalFieldUnramifiedExtensionExistence
import Dubon2026.FiniteGaloisEmbeddingStage
import Dubon2026.LocalFieldIntegerAlgEquiv

/-! # Actual unramified stages inside the original separably closed field -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Every positive degree occurs as an actual finite Galois intermediate
field of the original separably closed coefficient field. Its local topology
and extending valuation are constructed, and its actual integer extension is
proved unramified. No system of compatible stage valuations is asserted here. -/
theorem localField_exists_original_unramified_stage
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : ℕ) [NeZero n] :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E)
        (_ : IsNonarchimedeanLocalField E)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[E] ∧ Module.finrank K E = n := by
  obtain ⟨L, hField, hAlg, hVal, hTop, hLocal, hExt, hFinite, hGalois,
    hUnramified, hDegree⟩ := localField_exists_unramified_galois_extension K n
  letI : Field L := hField
  letI : Algebra K L := hAlg
  letI : ValuativeRel L := hVal
  letI : TopologicalSpace L := hTop
  haveI : IsNonarchimedeanLocalField L := hLocal
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := hExt
  haveI : FiniteDimensional K L := hFinite
  haveI : IsGalois K L := hGalois
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[L] := hUnramified
  let i : L →ₐ[K] Ω := IsSepClosed.lift
  let E := finiteGaloisEmbeddingStage i
  let e : L ≃ₐ[K] E := finiteGaloisEmbeddingStageEquiv i
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[E] :=
    localFieldIntegerAlgEquiv_formallyUnramified K L E e
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e.toLinearEquiv.finrank_eq.symm.trans hDegree⟩

end
end Dubon2026
