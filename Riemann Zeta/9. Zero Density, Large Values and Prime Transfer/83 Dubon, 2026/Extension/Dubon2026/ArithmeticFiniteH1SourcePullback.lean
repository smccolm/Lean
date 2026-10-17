import Dubon2026.ContinuousH1FinitePullback
import Dubon2026.ArithmeticFiniteStageTowerComparison
import Dubon2026.ArithmeticSourceRelationCupMaps

/-! # Actual finite H1 classes inflate to the original continuous source coefficient

The pinned H1 cocycles, continuous finite Galois restriction and actual
identity-on-values tower map construct the continuous representative. This
discharges the H1 input to DUB-17's finite-obstruction/cup comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Use the original rational inclusion of the arithmetic union. -/
local instance finiteH1SourceUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable (P N : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (hPN : P ≤ N)

/-- Use the original finite-stage rational inclusions. -/
local instance finiteH1SourceStageAlgebra
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Algebra ℚ F := F.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

/-- Every actual finite-stage H1 class has a continuous original-source
representative with the exact two-step arithmetic cohomology image. -/
theorem arithmeticFiniteStageH1_exists_source_pullback :
    letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
    letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
    letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
    letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
    letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(N/ℚ) :=
      AlgEquiv.restrictNormalHom N
    let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
      AlgEquiv.restrictNormalHom P
    let A := Rep.res σ B
    let BN := Rep.res τ B
    let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P N hPN B
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
    let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
    ∀ y : groupCohomology BN 1, ∃ x : arithmeticSourceRelationContinuousH1 Ω a P B,
      continuousH1ToAlgebraic A hA x =
        groupCohomology.map (MonoidHom.id _) β 1
          (groupCohomology.map π (𝟙 (Rep.res π BN)) 1 y) := by
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
  letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
  letI : IsScalarTower ℚ P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(N/ℚ) :=
    AlgEquiv.restrictNormalHom N
  let τ : Gal(N/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let σ : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res σ B
  let BN := Rep.res τ B
  let β := arithmeticFiniteRestrictionTowerComparison ℚ Ω a P N hPN B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  let hA := arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P B
  change ∀ y : groupCohomology BN 1, ∃ x : arithmeticSourceRelationContinuousH1 Ω a P B,
      continuousH1ToAlgebraic A hA x =
        groupCohomology.map (MonoidHom.id _) β 1
          (groupCohomology.map π (𝟙 (Rep.res π BN)) 1 y)
  intro y
  exact continuousH1_exists_finite_pullback_factor π
    (InfiniteGalois.restrictNormalHom_continuous N.toIntermediateField) BN A hA β y

end
end Dubon2026
