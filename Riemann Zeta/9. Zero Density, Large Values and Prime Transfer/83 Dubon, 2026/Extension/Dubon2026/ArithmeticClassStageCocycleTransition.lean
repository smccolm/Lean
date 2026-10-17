import Dubon2026.ArithmeticClassStageContinuousCocycle

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
local instance arithmeticClassStageCocycleTransitionLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology


/-- Transport an actual finite arithmetic class cocycle to a specified
larger stage by the original Galois restriction and class transition. -/
def arithmeticClassStageTwoCocycleTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F)
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E)) :
    groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha F) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  exact groupCohomology.mapCocycles₂ (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
    (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) c

/-- Placing the finite representative in a larger arithmetic coefficient
stage leaves its literal continuous cocycle unchanged. -/
theorem arithmeticClassStageContinuousTwoCocycle_transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F)
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E)) :
    arithmeticClassStageContinuousTwoCocycle K Ω a ha F
      (arithmeticClassStageTwoCocycleTransition K Ω a ha E F hEF c) =
        arithmeticClassStageContinuousTwoCocycle K Ω a ha E c := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply Subtype.ext
  apply Subtype.ext
  funext gh
  change (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
      ((arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom
        (c (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F gh.1),
          AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F gh.2)))) = _
  rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F gh.1,
    ← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F gh.2]
  exact Module.DirectLimit.of_f (R := ℤ)
    (G := fun L => arithmeticGlobalClassesModOutsideStageRep K Ω a ha L)
    (f := fun L M h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha L M h).hom.toLinearMap)
    (hij := hEF) (x := c (AlgEquiv.restrictNormalHom E gh.1, AlgEquiv.restrictNormalHom E gh.2))

end
end Dubon2026
