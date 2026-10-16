import Dubon2026.LocalFieldActualBaseChangeStage
import Dubon2026.SurjectiveBaseGaloisStage
import Dubon2026.SurjectiveBaseLocalStage
import Dubon2026.SurjectiveBaseValuationExtension
import Dubon2026.LocalFieldContinuousInvariantFiniteRestriction

/-! # The normalized invariant under the actual completion equivalence

A surjective local base map changes no field degree. Rebase an existing
unramified finite representative on its identical carrier, retaining its
valuation, and apply the proved finite invariant formula. This is exactly
the invariant transport needed from DUB-17's original completions to its
constructed arithmetic orbit fields.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] surjectiveBaseStageOriginalAlgebra surjectiveBaseStageTower

/-- The actual continuous local invariant is unchanged under a surjective compatible base-field map. -/
theorem localFieldContinuousInvariant_surjective_baseChange
    (K E Ω : Type) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [IsGalois K Ω] [IsGalois E Ω] [IsSepClosed Ω]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (h : Function.Surjective (algebraMap K E))
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      localFieldContinuousH2InvariantEquiv K Ω x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨F, hF, y, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  let G := surjectiveBaseGaloisStage K E Ω h F
  letI : Algebra K G := surjectiveBaseStageOriginalAlgebra K E Ω h F
  haveI : FiniteDimensional K G := F.finiteDimensional
  letI : IsScalarTower K E G := surjectiveBaseStageTower K E Ω h F
  letI : Algebra F G := Algebra.id F
  letI : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F G Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  letI : ValuativeRel G := surjectiveBaseLocalStageValuation K E Ω h F inferInstance
  letI : TopologicalSpace G := surjectiveBaseLocalStageTopology K E Ω h F inferInstance
  haveI : IsNonarchimedeanLocalField G := surjectiveBaseLocalStage_isLocal K E Ω h F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation G) :=
    inferInstanceAs ((ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F))
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G) :=
    inferInstanceAs ((ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation F))
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G) :=
    surjectiveBase_valuation_hasExtension K E G h
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[G] := hF
  haveI : IsScalarTower 𝒪[K] 𝒪[E] 𝒪[G] := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro z
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K E G (z : K))
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[G] :=
    Algebra.FormallyUnramified.of_restrictScalars 𝒪[K] 𝒪[E] 𝒪[G]
  have hd : Module.finrank K E = 1 := Module.finrank_of_bijective_algebraMap ⟨(algebraMap K E).injective, h⟩
  simpa only [hd, one_nsmul] using
    localFieldContinuousInvariant_actual_baseChange_stage K E Ω F G y

end
end Dubon2026
