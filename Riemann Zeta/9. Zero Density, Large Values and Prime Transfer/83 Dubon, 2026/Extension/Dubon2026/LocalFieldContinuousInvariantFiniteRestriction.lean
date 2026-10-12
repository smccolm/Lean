import Dubon2026.LocalFieldInvariantRestrictionGeneralStage
import Dubon2026.FiniteGaloisCompositumOverIntermediate
import Dubon2026.LocalFieldUnramifiedCompositum
import Dubon2026.SpectralOriginalUnramifiedStage
import Dubon2026.NormedLocalFieldCyclicCohomology
import Dubon2026.IntermediateFieldSupEmbeddings

/-! # Genuine finite separable restriction multiplies the full local invariant by the degree -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- For every original finite intermediate field of the separably
closed Galois coefficient field, actual continuous restriction multiplies
the full local invariant by the actual degree. The new base need not be
normal over K. The unramified representative and compositum are constructed
from the original class, and all local structures are the original ones. -/
theorem localFieldContinuousH2InvariantEquiv_finite_restriction
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
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
  let G := finiteGaloisCompositumOverIntermediate E F
  haveI : FiniteDimensional K G := FiniteDimensional.trans K E G
  letI : Algebra F G := (IntermediateField.inclusion
    (show F.toIntermediateField ≤ E ⊔ F.toIntermediateField from le_sup_right)).toAlgebra
  haveI : IsScalarTower K F G := .of_algebraMap_eq' rfl
  haveI : IsScalarTower F G Ω := .of_algebraMap_eq' rfl
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NontriviallyNormedField G := spectralNorm.nontriviallyNormedField K G
  letI : NormedAlgebra K G := spectralNorm.normedAlgebra K G
  letI : NormedAlgebra E G := spectralNorm.normedAlgebra' K E G
  letI : NormedAlgebra F G := spectralNorm.normedAlgebra' K F G
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist G := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : ValuativeRel G := ValuativeRel.ofValuation (NormedField.valuation (K := G))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : IsNonarchimedeanLocalField G := spectralFiniteExtension_isNonarchimedeanLocalField K G
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation G) :=
    normedFieldValuation_hasExtension E G
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation G) :=
    normedFieldValuation_hasExtension F G
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[G] :=
    localField_integer_unramified_of_compositum K E F G
      (intermediateField_sup_inclusion_ranges E F.toIntermediateField)
  exact localFieldContinuousInvariant_restriction_general_stage K Ω E F G y

end
end Dubon2026
