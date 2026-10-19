import Dubon2026.ArithmeticFiniteSUnitHomH1
import Dubon2026.ArithmeticFiniteSUnitLocalConnecting

/-! The actual finite arithmetic unit-Hom localization on continuous H1.
This names the native restricted dual-diagram map for the direct class
constructed from DUB-17's finite correction; continuity is derived. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  arithmeticUnitMapAlgebra

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B] (p : ℕ) (hp : p.Prime)

/-- Continuous H1 of the actual restricted finite unit-Hom coefficient. -/
abbrev ArithmeticPrimeRestrictedUnitHomH1 :=
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  let U := arithmeticPrimeRestrictedUnitHom a F B p hp
  letI : TopologicalSpace U := ⊥
  letI : DiscreteTopology U := ⟨rfl⟩
  letI : @ContinuousSMul ℤ U U.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ U U.hV2.toSMul _ _ continuous_of_discreteTopology
  ContinuousRepresentationH1 U (arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp)

/-- Restrict the actual finite unit-Hom H1 and apply the original arithmetic
localization morphism of its native dual diagram. -/
def arithmeticFiniteSUnitLocalH1Map :
    ArithmeticFiniteSUnitHomH1 a ha F B →ₗ[ℤ] ArithmeticPrimeRestrictedUnitHomH1 a F B p hp := by
  let A := arithmeticFiniteSUnitHomRep a ha F B
  let U := arithmeticPrimeRestrictedUnitHom a F B p hp
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace U := ⊥
  letI : DiscreteTopology U := ⟨rfl⟩
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ U U.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ U U.hV2.toSMul _ _ continuous_of_discreteTopology
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let hj := (rationalPrimeArithmeticRestriction a p hp).continuous
  let d := arithmeticFiniteSUnitLocalDualDiagram a ha F B p hp
  let hA := arithmeticFiniteSUnitHomAction_continuous a ha F B
  let hU := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp
  exact (continuousCoefficientH1Map (restrictedCoefficientRep A j) U d.τ₁.hom.toLinearMap
    continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
    (restrictedCoefficientAction_continuous A j hj hA) hU).comp
      (continuousRepresentationH1Restriction A hA j hj)

end
end Dubon2026
