import Dubon2026.ArithmeticFiniteSUnitDualConnecting
import Dubon2026.RationalTraceFiniteTowerAction

/-! Name the actual finite arithmetic S-unit Hom H1 already used by the
native connecting construction. Its action continuity is derived from
the original finite coefficient and arithmetic S-units. This allows the
returned finite correction to feed the actual Galois-tower comparison
on DUB-17's reverse-localization chain. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ))

/-- The original global unit-Hom coefficient of the actual finite stage. -/
abbrev arithmeticFiniteSUnitHomRep :=
  (Rep.ihom (Rep.res (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)) B)).obj
    (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha)

/-- Retain the native discrete topology on the finite arithmetic unit-Hom. -/
local instance arithmeticFiniteSUnitHomTopology :
    TopologicalSpace (arithmeticFiniteSUnitHomRep a ha F B) := ⊥
local instance arithmeticFiniteSUnitHomDiscrete :
    DiscreteTopology (arithmeticFiniteSUnitHomRep a ha F B) := ⟨rfl⟩
local instance arithmeticFiniteSUnitHomContinuousSMul :
    @ContinuousSMul ℤ (arithmeticFiniteSUnitHomRep a ha F B)
      (arithmeticFiniteSUnitHomRep a ha F B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticFiniteSUnitHomRep a ha F B)
    (arithmeticFiniteSUnitHomRep a ha F B).hV2.toSMul _ _ continuous_of_discreteTopology

variable [Finite B]

/-- The original finite coefficient gives continuous unit-Hom action;
no continuity premise is supplied by the finite correction. -/
theorem arithmeticFiniteSUnitHomAction_continuous :
    Continuous (fun z : rationalArithmeticGaloisGroup a × arithmeticFiniteSUnitHomRep a ha F B =>
      (arithmeticFiniteSUnitHomRep a ha F B).ρ z.1 z.2) := by
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let C := Rep.res π B
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  letI : Finite C := inferInstanceAs (Finite B)
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : TopologicalSpace ((Rep.ihom C).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom C).obj D) := ⟨rfl⟩
  exact originalInternalHomAction_continuous_of_finite C D
    (arithmeticFiniteStageRepresentationAction_continuous ℚ (AlgebraicClosure ℚ) a F B)
    (originalArithmeticSUnitAction_continuous ℚ (AlgebraicClosure ℚ) a ha)

/-- Continuous H1 of the actual finite arithmetic unit-Hom coefficient. -/
abbrev ArithmeticFiniteSUnitHomH1 :=
  ContinuousRepresentationH1 (arithmeticFiniteSUnitHomRep a ha F B)
    (arithmeticFiniteSUnitHomAction_continuous a ha F B)

end
end Dubon2026
