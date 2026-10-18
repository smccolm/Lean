import Dubon2026.GaloisTowerLocalRelationFiniteComparison
import Dubon2026.ContinuousFiniteCoefficientObstructionComparison

/-! The finite local relation class retains its exact algebraic connecting
obstruction. This is the finite comparison used inside the native full-idele
completion invariant; no infinite forgetful-map injectivity is needed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] finiteLocalRelationKernelTopology finiteLocalRelationKernelDiscrete
  finiteLocalRelationKernelContinuousSMul finiteLocalRelationFreeTopology finiteLocalRelationFreeDiscrete
  finiteLocalRelationFreeContinuousSMul finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L]
  (H : Type) [Group H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H)

/-- The same finite local relation connecting class has precisely its original algebraic obstruction. -/
theorem galoisTowerFiniteLocalRelationConnecting_toAlgebraic
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B) :
    continuousH2ToAlgebraic (Rep.ofAlgebraAutOnUnits K L)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
      (galoisTowerFiniteLocalRelationConnecting K L H ι B ψ x) =
    (groupCohomology.functor ℤ Gal(L/K) 2).map ψ
      (groupCohomology.δ (originalRelationGroupChange_shortExact ι B) 1 2 rfl
        (continuousH1ToAlgebraic (Rep.res ι B) continuous_of_discreteTopology x)) := by
  let X := galoisTowerFiniteLocalRelationComplex K L H ι B
  let C := Rep.ofAlgebraAutOnUnits K L
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ X.X₁.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ X.X₁.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₂ X.X₂.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ X.X₂.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₃ X.X₃.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ X.X₃.hV2.toSMul _ _ continuous_of_discreteTopology
  exact continuousShortComplexCoefficientObstruction_toAlgebraic X
    (originalRelationGroupChange_shortExact ι B) C
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) ψ x

end
end Dubon2026
