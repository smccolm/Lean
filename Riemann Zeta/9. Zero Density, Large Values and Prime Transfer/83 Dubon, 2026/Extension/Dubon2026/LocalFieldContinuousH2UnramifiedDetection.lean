import Dubon2026.SpectralFiniteStageUnramifiedH2Detection
import Dubon2026.ContinuousGaloisUnitH2FiniteStage

/-! # Every original local continuous H2 class has an actual unramified representative -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Every original continuous unit H2 class comes from an actual finite
unramified Galois subfield of the original separably closed coefficient field.
All extending local structures are constructed on that same subfield. -/
theorem localField_continuousH2_exists_unramified_stage
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F)
        (_ : IsNonarchimedeanLocalField F)
        (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)),
        Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
          letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
          letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
          ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
            galoisUnitFiniteStageH2Inflation F y = x := by
  obtain ⟨E, y, hy⟩ := continuousGaloisUnitH2_exists_finite_stage x
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨F, _, hF, z, hz⟩ := spectralFiniteStageH2_exists_unramified_representative E y
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, hF, z, hz.symm.trans hy⟩

end
end Dubon2026
