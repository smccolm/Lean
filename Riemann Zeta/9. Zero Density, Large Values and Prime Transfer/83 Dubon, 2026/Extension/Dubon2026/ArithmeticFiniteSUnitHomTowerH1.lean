import Dubon2026.ArithmeticFiniteSUnitHomH1
import Dubon2026.ArithmeticUnitHomTowerCoefficient
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! The literal tower coefficient map identifies the actual arithmetic
S-unit Hom H1 at the returned correction field with that at the source
coefficient field. This supplies the direct global-class construction
on DUB-17's prescribed-restriction chain with no new action premise. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  arithmeticFiniteSUnitHomTopology arithmeticFiniteSUnitHomDiscrete arithmeticFiniteSUnitHomContinuousSMul

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) [Finite B]


/-- The actual tower identifies the two arithmetic unit-Hom H1 spaces. -/
def arithmeticFiniteSUnitHomTowerH1Equiv :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    ArithmeticFiniteSUnitHomH1 a ha L BL ≃+ ArithmeticFiniteSUnitHomH1 a ha M B := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  let UL := arithmeticFiniteSUnitHomRep a ha L BL
  let UM := arithmeticFiniteSUnitHomRep a ha M B
  letI : TopologicalSpace UL := ⊥
  letI : DiscreteTopology UL := ⟨rfl⟩
  letI : TopologicalSpace UM := ⊥
  letI : DiscreteTopology UM := ⟨rfl⟩
  letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let j := MonoidHom.id (rationalArithmeticGaloisGroup a)
  let e := arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D
  let he := arithmeticUnitHomTowerCoefficientEquiv_equivariant a M L hML B j D
  let hL := arithmeticFiniteSUnitHomAction_continuous a ha L BL
  let hM := arithmeticFiniteSUnitHomAction_continuous a ha M B
  change ArithmeticFiniteSUnitHomH1 a ha L BL ≃+ ArithmeticFiniteSUnitHomH1 a ha M B
  exact continuousH1AdditiveCoefficientEquiv UL UM e
    continuous_of_discreteTopology continuous_of_discreteTopology he hL hM

/-- The tower H1 identification retains the literal coefficient cocycle. -/
theorem arithmeticFiniteSUnitHomTowerH1Equiv_mk :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    let UL := arithmeticFiniteSUnitHomRep a ha L BL
    let UM := arithmeticFiniteSUnitHomRep a ha M B
    letI : TopologicalSpace UL := ⊥
    letI : DiscreteTopology UL := ⟨rfl⟩
    letI : TopologicalSpace UM := ⊥
    letI : DiscreteTopology UM := ⟨rfl⟩
    letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
    letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
    let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
    let j := MonoidHom.id (rationalArithmeticGaloisGroup a)
    let e := arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D
    let he := arithmeticUnitHomTowerCoefficientEquiv_equivariant a M L hML B j D
    ∀ c : continuousRepresentationCocyclesOne UL,
    arithmeticFiniteSUnitHomTowerH1Equiv a ha M L hML B (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv UL UM e
        continuous_of_discreteTopology continuous_of_discreteTopology he c) := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  let UL := arithmeticFiniteSUnitHomRep a ha L BL
  let UM := arithmeticFiniteSUnitHomRep a ha M B
  letI : TopologicalSpace UL := ⊥
  letI : DiscreteTopology UL := ⟨rfl⟩
  letI : TopologicalSpace UM := ⊥
  letI : DiscreteTopology UM := ⟨rfl⟩
  letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let j := MonoidHom.id (rationalArithmeticGaloisGroup a)
  let e := arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D
  let he := arithmeticUnitHomTowerCoefficientEquiv_equivariant a M L hML B j D
  let hL := arithmeticFiniteSUnitHomAction_continuous a ha L BL
  let hM := arithmeticFiniteSUnitHomAction_continuous a ha M B
  change ∀ c : continuousRepresentationCocyclesOne UL, _
  intro c
  exact continuousH1AdditiveCoefficientEquiv_mk UL UM e
    continuous_of_discreteTopology continuous_of_discreteTopology he hL hM c

end
end Dubon2026
