import Dubon2026.GaloisUnitFiniteStageInflation
import Dubon2026.GaloisUnitTwoCocycleFiniteDescent

/-! # Every original continuous Galois unit H2 class comes from an actual finite stage -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Actual finite descent of the original two-cocycle supplies a genuine H2
class over a constructed finite Galois field. Its original inflation equals
the original class, with the actual Krull topologies unchanged. -/
theorem continuousGaloisUnitH2_exists_finite_stage
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
        galoisUnitFiniteStageH2Inflation F y = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨F, hvalues, hperiod⟩ := continuousGaloisUnitTwoCocycle_exists_finiteField c
    obtain ⟨f, hf, hfactor⟩ :=
      galoisUnitTwoCocycle_exists_finite_descent F c.val hvalues hperiod
    refine ⟨F, ?_⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    let cF : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F) :=
      ⟨groupCohomology.cocyclesOfIsMulCocycle₂ hf, continuous_of_discreteTopology⟩
    refine ⟨Submodule.Quotient.mk cF, ?_⟩
    rw [galoisUnitFiniteStageH2Inflation_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact hfactor z.1 z.2

end
end Dubon2026
