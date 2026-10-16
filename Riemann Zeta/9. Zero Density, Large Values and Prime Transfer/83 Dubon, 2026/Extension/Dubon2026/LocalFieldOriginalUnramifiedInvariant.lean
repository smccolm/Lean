import Dubon2026.OriginalFiniteGaloisImageInflation
import Dubon2026.LocalFieldContinuousInvariantNormalization
import Dubon2026.LocalFieldInvariantBaseChange
import Dubon2026.LocalFieldIntegerAlgEquiv

/-! # The original unramified finite-class invariant is independent of its image

Identify the actual finite field with its literal image in the closure.
Existing integer-ring transport preserves unramifiedness, and the proved
finite degree formula preserves the original period. This is the entry
needed to compare the closure choices in DUB-17's canonical prime sum.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- Inflating an actual unramified finite local class into the chosen closure has its original arithmetic-Frobenius period. -/
theorem localFieldOriginalUnramified_invariant
    (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    localFieldContinuousH2InvariantEquiv K Ω (continuousGaloisUnitBaseChangeH2 K K L Ω x) =
      localFieldPeriodRationalInvariant K L x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  obtain ⟨hval, htop⟩ := localField_local_structures_eq_spectral K L
  cases hval
  cases htop
  let F := originalFiniteGaloisImage K L Ω
  letI := originalFiniteGaloisImageAlgebra K L Ω
  letI := originalFiniteGaloisImage_baseTower K L Ω
  letI := originalFiniteGaloisImage_ambientTower K L Ω
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NormedAlgebra L F := spectralNorm.normedAlgebra' K L F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation F) :=
    normedFieldValuation_hasExtension L F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] :=
    localFieldIntegerAlgEquiv_formallyUnramified K L F (originalFiniteGaloisImageEquiv K L Ω)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  have hi := originalFiniteGaloisImage_inflation K L Ω x
  have hs := localFieldContinuousH2InvariantEquiv_stage K Ω F
    (finiteGaloisUnitBaseChangeH2 K K L F x)
  have hb := localFieldPeriodRationalInvariant_baseChange K K L F x
  have hb' : localFieldPeriodRationalInvariant K F (finiteGaloisUnitBaseChangeH2 K K L F x) =
      localFieldPeriodRationalInvariant K L x := by
    simpa only [Module.finrank_self, one_nsmul] using hb
  exact (congrArg (localFieldContinuousH2InvariantEquiv K Ω) hi).symm.trans (hs.trans hb')

end
end Dubon2026
