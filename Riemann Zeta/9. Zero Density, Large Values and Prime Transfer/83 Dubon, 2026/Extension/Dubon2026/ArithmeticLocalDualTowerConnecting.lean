import Dubon2026.ArithmeticLocalDualTowerDiagram
import Dubon2026.ContinuousInvariantConnectingNaturality
import Dubon2026.OriginalGaloisRestrictionTowerDiagram
import Dubon2026.RationalTraceFiniteTowerAction

/-! Compare the actual local dual connecting classes through the original
finite field tower. The native presentation map is reused; local dual
exactness and continuity are derived. This supplies the tower edge needed
to recover DUB-17's prescribed local classes from the finite correction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) [Finite B] (hCoeff : ∀ b : B, q • b = 0)
  (p : ℕ) (hp : p.Prime)

/-- The exact local dual connecting square of the original finite tower. -/
abbrev ArithmeticLocalDualTowerConnectingCompatibility : Prop :=
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra;
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule;
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul;
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M;
    let BL := Rep.res τ B;
    let YM := arithmeticPrimeLocalUnitDualSequence a M B p hp;
    let YL := arithmeticPrimeLocalUnitDualSequence a L BL p hp;
    let d := arithmeticLocalDualTowerDiagram a M L hML B p hp;
    letI : Finite BL := inferInstanceAs (Finite B);
    letI : Module.Finite ℤ B := Module.Finite.of_finite;
    letI : Module.Finite ℤ BL := Module.Finite.of_finite;
    letI : TopologicalSpace YM.X₁ := ⊥;
    letI : DiscreteTopology YM.X₁ := ⟨rfl⟩;
    letI : TopologicalSpace YL.X₁ := ⊥;
    letI : DiscreteTopology YL.X₁ := ⟨rfl⟩;
    letI : @ContinuousSMul ℤ YM.X₁ (YM.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ YM.X₁ (YM.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    letI : @ContinuousSMul ℤ YL.X₁ (YL.X₁).hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ YL.X₁ (YL.X₁).hV2.toSMul _ _ continuous_of_discreteTopology;
    let hM1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp inferInstance ⊥ ⟨rfl⟩;
    let hL1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp inferInstance ⊥ ⟨rfl⟩;
    ∀ w : YM.X₃.ρ.invariants,
    let wL : YL.X₃.ρ.invariants := ⟨d.τ₃.hom w.val, fun g =>
      (Rep.hom_comm_apply d.τ₃ g w.val).symm.trans (congrArg d.τ₃.hom (w.property g))⟩
    continuousCoefficientH1Map YM.X₁ YL.X₁ d.τ₁.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁) hM1 hL1
      (arithmeticPrimeLocalUnitDualConnecting a M B p hp q hCoeff w) =
      arithmeticPrimeLocalUnitDualConnecting a L BL p hp q (fun b => hCoeff b) wL

/-- The original finite relation tower preserves its actual local
dual connecting class through the native presentation map; no diagram,
dual exactness or action-continuity input remains to be supplied. -/
theorem arithmeticLocalDualConnecting_tower :
    ArithmeticLocalDualTowerConnectingCompatibility a q M L hML B hCoeff p hp := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  let YM := arithmeticPrimeLocalUnitDualSequence a M B p hp
  let YL := arithmeticPrimeLocalUnitDualSequence a L BL p hp
  let d := arithmeticLocalDualTowerDiagram a M L hML B p hp
  letI : Finite BL := inferInstanceAs (Finite B)
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ BL := Module.Finite.of_finite
  letI : Module.Finite ℤ (Rep.free ℤ Gal(M/ℚ) B) := by
    change Module.Finite ℤ (B →₀ Gal(M/ℚ) →₀ ℤ)
    infer_instance
  letI : Module.Finite ℤ (Rep.free ℤ Gal(L/ℚ) BL) := by
    change Module.Finite ℤ (BL →₀ Gal(L/ℚ) →₀ ℤ)
    infer_instance
  letI : TopologicalSpace YM.X₁ := ⊥
  letI : DiscreteTopology YM.X₁ := ⟨rfl⟩
  letI : TopologicalSpace YM.X₂ := ⊥
  letI : DiscreteTopology YM.X₂ := ⟨rfl⟩
  letI : TopologicalSpace YL.X₁ := ⊥
  letI : DiscreteTopology YL.X₁ := ⟨rfl⟩
  letI : TopologicalSpace YL.X₂ := ⊥
  letI : DiscreteTopology YL.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ YM.X₁ (YM.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ YM.X₁ (YM.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ YL.X₁ (YL.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ YL.X₁ (YL.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  let hM1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a M B p hp inferInstance ⊥ ⟨rfl⟩
  let hM2 := @arithmeticPrimeRestrictedUnitHomAction_continuous a M (Rep.free ℤ Gal(M/ℚ) B) p hp inferInstance ⊥ ⟨rfl⟩
  let hYM := arithmeticPrimeLocalUnitDualSequence_shortExact a M B p hp q (fun b => hCoeff b)
  let hL1 := @arithmeticPrimeRestrictedUnitHomAction_continuous a L BL p hp inferInstance ⊥ ⟨rfl⟩
  let hL2 := @arithmeticPrimeRestrictedUnitHomAction_continuous a L (Rep.free ℤ Gal(L/ℚ) BL) p hp inferInstance ⊥ ⟨rfl⟩
  let hYL := arithmeticPrimeLocalUnitDualSequence_shortExact a L BL p hp q (fun b => hCoeff b)
  change ∀ w : YM.X₃.ρ.invariants, _
  intro w
  exact continuousInvariantConnecting_naturality YM YL hYM hYL hM1 hM2 hL1 hL2
    d continuous_of_discreteTopology w

end
end Dubon2026
