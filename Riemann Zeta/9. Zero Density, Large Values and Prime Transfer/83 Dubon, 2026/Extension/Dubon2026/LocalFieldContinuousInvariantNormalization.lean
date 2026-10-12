import Dubon2026.LocalFieldContinuousH2Invariant
import Dubon2026.SpectralInvariantOriginalPeriod

/-! # The full local invariant has the original arithmetic-Frobenius normalization -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- On every actual unramified finite subfield, the full invariant
is the literal arithmetic-Frobenius period computed with the supplied
original local structures, independent of the spectral construction. -/
theorem localFieldContinuousH2InvariantEquiv_stage
    (F : FiniteGaloisIntermediateField K Ω)
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]] (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    localFieldContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      localFieldPeriodRationalInvariant K F x := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  have hF : SpectralStageUnramified K Ω F := spectralIntegerExtension_formallyUnramified K F
  exact (spectralContinuousH2InvariantEquiv_stage K Ω F hF x).trans
    (spectralUnramifiedStageInvariant_eq_original_period K Ω F hF x)

end
end Dubon2026
