import Dubon2026.ArithmeticClassStageFiniteZeroWitness

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
local instance arithmeticClassStageFiniteEqualityWitnessLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- The literal arithmetic continuous inflation preserves subtraction of
finite cocycles, with the same field restriction and coefficient map. -/
theorem arithmeticClassStageContinuousTwoCocycle_sub
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c d : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E)) :
    arithmeticClassStageContinuousTwoCocycle K Ω a ha E (c - d) =
      arithmeticClassStageContinuousTwoCocycle K Ω a ha E c -
        arithmeticClassStageContinuousTwoCocycle K Ω a ha E d := by
  apply Subtype.ext
  apply Subtype.ext
  funext gh
  exact map_sub (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom _ _

/-- Equality of the literal continuous class images constructs a common
larger finite arithmetic stage where the actual finite H2 classes agree. -/
theorem arithmeticClassStageContinuousH2_eq_exists_finite_witness
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c d : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E))
    (hcd : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E c) :
      ContinuousRepresentationH2 (arithmeticClassesModOutsideColimitRep K Ω a ha)
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)) =
          Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E d)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEF : E ≤ F,
        letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
        letI : Module E F := Algebra.toModule
        letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
        letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
        letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
          IsScalarTower.of_algebraMap_eq' rfl
        groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
          (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) 2
          (groupCohomology.H2π _ c) =
        groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
          (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) 2
          (groupCohomology.H2π _ d) := by
  have hz : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E (c - d)) :
      ContinuousRepresentationH2 (arithmeticClassesModOutsideColimitRep K Ω a ha)
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)) = 0 := by
    let q := (continuousRepresentationCoboundariesTwo
      (arithmeticClassesModOutsideColimitRep K Ω a ha)
      (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)).mkQ
    exact (congrArg q (arithmeticClassStageContinuousTwoCocycle_sub K Ω a ha E c d)).trans
      ((map_sub q _ _).trans (sub_eq_zero.mpr hcd))
  obtain ⟨F, hEF, hF⟩ := arithmeticClassStageContinuousH2_zero_exists_finite_witness K Ω a ha E (c - d) hz
  refine ⟨F, hEF, ?_⟩
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact sub_eq_zero.mp ((map_sub
    (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
      (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) 2).hom
      (groupCohomology.H2π _ c) (groupCohomology.H2π _ d)).symm.trans
        ((congrArg (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
          (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) 2)
          (map_sub (groupCohomology.H2π _).hom c d).symm).trans hF))

end
end Dubon2026
