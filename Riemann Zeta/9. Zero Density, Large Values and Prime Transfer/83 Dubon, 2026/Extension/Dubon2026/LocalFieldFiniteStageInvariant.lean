import Dubon2026.SpectralFiniteStageInvariantRange
import Dubon2026.LocalFieldContinuousH2Invariant

/-! # The relative invariant for every original finite Galois local extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The relative invariant is the original local invariant after
genuine inflation of the original finite Galois unit cocycles. -/
def localFieldFiniteStageInvariant (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (localFieldContinuousH2InvariantEquiv K Ω).toLinearMap.comp
    (galoisUnitH2FiniteStageMap K Ω E)

/-- Original relative invariants detect equality of actual finite
Galois classes. No norm is supplied as a premise. -/
theorem localFieldFiniteStageInvariant_injective (E : FiniteGaloisIntermediateField K Ω) :
    Function.Injective (localFieldFiniteStageInvariant K Ω E) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact (localFieldContinuousH2InvariantEquiv K Ω).injective.comp
    (galoisUnitFiniteStageH2Inflation_injective E)

/-- The exact image for any original local field and original finite
Galois stage is the degree annihilator in the rational circle. -/
theorem localFieldFiniteStageInvariant_mem_range_iff
    (E : FiniteGaloisIntermediateField K Ω) (q : AddCircle (1 : ℚ)) :
    q ∈ (localFieldFiniteStageInvariant K Ω E).range ↔ Module.finrank K E • q = 0 := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  exact spectralFiniteStageFullInvariant_mem_range_iff K Ω E q

/-- The original relative invariant is unchanged by the genuine
finite-field cocycle inflation transition. -/
theorem localFieldFiniteStageInvariant_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    (x : GaloisUnitH2FiniteStage K Ω E) :
    localFieldFiniteStageInvariant K Ω F (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      localFieldFiniteStageInvariant K Ω E x := by
  change localFieldContinuousH2InvariantEquiv K Ω
    (galoisUnitH2FiniteStageMap K Ω F (galoisUnitH2FiniteTransition K Ω E F hEF x)) = _
  rw [galoisUnitH2FiniteStageMap_transition]
  rfl

end
end Dubon2026
