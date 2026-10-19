import Dubon2026.ArithmeticLocalDualTowerDiagram
import Dubon2026.ArithmeticUnitHomTowerCoefficient
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! The literal tower coefficient equivalence identifies the actual
prime-local unit-Hom H1 and cancels the native forward dual diagram map.
This is the local tower edge for DUB-17's direct finite-correction class. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
  arithmeticUnitMapAlgebra

variable (a : 𝓞 ℚ)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) [Finite B] (p : ℕ) (hp : p.Prime)

/-- The actual arithmetic tower identifies prime-local unit-Hom H1. -/
def arithmeticPrimeUnitHomTowerH1Equiv :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : Module.Finite ℤ BL := Module.Finite.of_finite
    let UM := arithmeticPrimeRestrictedUnitHom a M B p hp
    let UL := arithmeticPrimeRestrictedUnitHom a L BL p hp
    letI : TopologicalSpace UM := ⊥
    letI : DiscreteTopology UM := ⟨rfl⟩
    letI : TopologicalSpace UL := ⊥
    letI : DiscreteTopology UL := ⟨rfl⟩
    letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
    letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
    let hM := arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp
    let hL := arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp
    ContinuousRepresentationH1 UL hL ≃+ ContinuousRepresentationH1 UM hM := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ BL := Module.Finite.of_finite
  let UM := arithmeticPrimeRestrictedUnitHom a M B p hp
  let UL := arithmeticPrimeRestrictedUnitHom a L BL p hp
  letI : TopologicalSpace UM := ⊥
  letI : DiscreteTopology UM := ⟨rfl⟩
  letI : TopologicalSpace UL := ⊥
  letI : DiscreteTopology UL := ⟨rfl⟩
  letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
  let hM := arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp
  let hL := arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let D := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  let e := arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D
  let he := arithmeticUnitHomTowerCoefficientEquiv_equivariant a M L hML B j D
  change ContinuousRepresentationH1 UL hL ≃+ ContinuousRepresentationH1 UM hM
  exact continuousH1AdditiveCoefficientEquiv UL UM e
    continuous_of_discreteTopology continuous_of_discreteTopology he hL hM

/-- The backwards tower identification cancels the original forward
local dual diagram map on every actual continuous H1 class. -/
theorem arithmeticPrimeUnitHomTowerH1Equiv_map :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : Module.Finite ℤ BL := Module.Finite.of_finite
    let UM := arithmeticPrimeRestrictedUnitHom a M B p hp
    let UL := arithmeticPrimeRestrictedUnitHom a L BL p hp
    letI : TopologicalSpace UM := ⊥
    letI : DiscreteTopology UM := ⟨rfl⟩
    letI : TopologicalSpace UL := ⊥
    letI : DiscreteTopology UL := ⟨rfl⟩
    letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
    letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
    let hM := arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp
    let hL := arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp
    let d := arithmeticLocalDualTowerDiagram a M L hML B p hp
    ∀ x : ContinuousRepresentationH1 UM hM,
    arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p hp
      (continuousCoefficientH1Map UM UL d.τ₁.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁) hM hL x) = x := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ BL := Module.Finite.of_finite
  let UM := arithmeticPrimeRestrictedUnitHom a M B p hp
  let UL := arithmeticPrimeRestrictedUnitHom a L BL p hp
  letI : TopologicalSpace UM := ⊥
  letI : DiscreteTopology UM := ⟨rfl⟩
  letI : TopologicalSpace UL := ⊥
  letI : DiscreteTopology UL := ⟨rfl⟩
  letI : @ContinuousSMul ℤ UM UM.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UM UM.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ UL UL.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ UL UL.hV2.toSMul _ _ continuous_of_discreteTopology
  let hM := arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp
  let hL := arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp
  let d := arithmeticLocalDualTowerDiagram a M L hML B p hp
  change ∀ x : ContinuousRepresentationH1 UM hM,
    arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p hp
      (continuousCoefficientH1Map UM UL d.τ₁.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁) hM hL x) = x
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk c
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro b
    rfl

end
end Dubon2026
