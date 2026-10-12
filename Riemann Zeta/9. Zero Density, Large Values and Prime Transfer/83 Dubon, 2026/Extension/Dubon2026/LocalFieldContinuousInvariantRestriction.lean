import Dubon2026.LocalFieldInvariantRestrictionOnStage
import Dubon2026.SpectralRebasedUnramifiedSup

/-! # Actual finite Galois restriction multiplies the full local invariant by the degree -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- For every original finite Galois subfield E of the original
separably closed coefficient field, genuine continuous restriction multiplies
the full arithmetic invariant by the actual degree E/K. The representative
and unramified compositum are constructed from the original class. -/
theorem localFieldContinuousH2InvariantEquiv_restriction
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨hval, htop⟩ := localField_local_structures_eq_spectral K E
  cases hval
  cases htop
  obtain ⟨F, hF, y, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  let H := E ⊔ F
  letI : Algebra E H := inferInstanceAs
    (Algebra E (finiteGaloisStageExtendScalars E H le_sup_left))
  letI : Algebra F H := (IntermediateField.inclusion
    (show F.toIntermediateField ≤ H.toIntermediateField from le_sup_right)).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := .of_algebraMap_eq' rfl
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
  letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
  letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
  letI : NormedAlgebra F H := spectralNorm.normedAlgebra' K F H
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : IsNonarchimedeanLocalField H := spectralFiniteExtension_isNonarchimedeanLocalField K H
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension E H
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension F H
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[H] := spectralFiniteGalois_sup_rebased_unramified E F hF
  exact localFieldContinuousInvariant_restriction_on_stage K Ω E F H le_sup_left le_sup_right
    (_hextEH := normedFieldValuation_hasExtension E H)
    (_hextFH := normedFieldValuation_hasExtension F H)
    (_hunram := spectralFiniteGalois_sup_rebased_unramified E F hF) y

end
end Dubon2026
