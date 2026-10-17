import Dubon2026.ArithmeticClassStageCocycleComposition
import Dubon2026.ArithmeticClassStageFiniteEqualityWitness

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticClassStageCommonEqualityLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- Two original finite class representatives with equal continuous H2
images become equal at one actual finite Galois stage containing both.
The stage and equality are constructed by continuous coboundary descent. -/
theorem arithmeticClassStagesContinuousH2_eq_exists_common_finite_witness
    (E D : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E))
    (d : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha D))
    (hcd : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E c) :
      ContinuousRepresentationH2 (arithmeticClassesModOutsideColimitRep K Ω a ha)
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)) =
          Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha D d)) :
    ∃ M : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEM : E ≤ M, ∃ hDM : D ≤ M,
        groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition K Ω a ha E M hEM c) =
          groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition K Ω a ha D M hDM d) := by
  let J := E ⊔ D
  have hEJ : E ≤ J := le_sup_left
  have hDJ : D ≤ J := le_sup_right
  let cJ := arithmeticClassStageTwoCocycleTransition K Ω a ha E J hEJ c
  let dJ := arithmeticClassStageTwoCocycleTransition K Ω a ha D J hDJ d
  let q := (continuousRepresentationCoboundariesTwo
    (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)).mkQ
  have hJ : q (arithmeticClassStageContinuousTwoCocycle K Ω a ha J cJ) =
      q (arithmeticClassStageContinuousTwoCocycle K Ω a ha J dJ) :=
    (congrArg q (arithmeticClassStageContinuousTwoCocycle_transition K Ω a ha E J hEJ c)).trans
      (hcd.trans (congrArg q
        (arithmeticClassStageContinuousTwoCocycle_transition K Ω a ha D J hDJ d)).symm)
  obtain ⟨M, hJM, hM⟩ := arithmeticClassStageContinuousH2_eq_exists_finite_witness
    K Ω a ha J cJ dJ hJ
  letI : Algebra J M := (IntermediateField.inclusion hJM).toAlgebra
  letI : Module J M := Algebra.toModule
  letI : SMul J M := ((IntermediateField.inclusion hJM).toAlgebra).toSMul
  letI : IsScalarTower K J M := IsScalarTower.of_algHom (IntermediateField.inclusion hJM)
  letI : IsScalarTower J M (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hm : groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition K Ω a ha J M hJM cJ) =
      groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition K Ω a ha J M hJM dJ) :=
    (groupCohomology.H2π_comp_map_apply (AlgEquiv.restrictNormalHom J : Gal(M/K) →* Gal(J/K))
      (arithmeticClassesModOutsideFiniteTransition K Ω a ha J M hJM) cJ).symm.trans
        (hM.trans (groupCohomology.H2π_comp_map_apply
          (AlgEquiv.restrictNormalHom J : Gal(M/K) →* Gal(J/K))
          (arithmeticClassesModOutsideFiniteTransition K Ω a ha J M hJM) dJ))
  refine ⟨M, hEJ.trans hJM, hDJ.trans hJM, ?_⟩
  exact (congrArg (groupCohomology.H2π _)
    (arithmeticClassStageTwoCocycleTransition_comp K Ω a ha E J M hEJ hJM c)).symm.trans
      (hm.trans (congrArg (groupCohomology.H2π _)
        (arithmeticClassStageTwoCocycleTransition_comp K Ω a ha D J M hDJ hJM d)))

end
end Dubon2026
