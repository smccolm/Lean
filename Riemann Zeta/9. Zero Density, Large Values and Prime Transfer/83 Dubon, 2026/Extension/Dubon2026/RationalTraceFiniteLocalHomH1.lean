import Dubon2026.RationalTraceFiniteLocalHomCoefficient

/-! The exact local finite coefficient identification on continuous H1.
This links the finite S-unit connecting class to the original prime-local
trace Hom before applying DUB-17's prescribed-class comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois


variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)



local instance finiteLocalTraceCoefficientFinite :
    Finite (rationalTraceOriginalFiniteRep a q σ F hker) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
local instance finiteLocalTraceCoefficientModuleFinite :
    Module.Finite ℤ (rationalTraceOriginalFiniteRep a q σ F hker) := Module.Finite.of_finite
/-- Retain the discrete topology of the actual finite local Hom coefficient. -/
local instance finiteLocalTraceHomTopology :
    TopologicalSpace (rationalTraceFiniteLocalHomRep a q σ F hker p hp) := ⊥
local instance finiteLocalTraceHomDiscrete :
    DiscreteTopology (rationalTraceFiniteLocalHomRep a q σ F hker p hp) := ⟨rfl⟩
local instance finiteLocalTraceHomContinuousSMul :
    @ContinuousSMul ℤ (rationalTraceFiniteLocalHomRep a q σ F hker p hp)
      (rationalTraceFiniteLocalHomRep a q σ F hker p hp).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- Retain the original discrete prime-local trace-Hom topology. -/
local instance finiteLocalPrimeHomTopology : TopologicalSpace
    (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))) := ⊥
local instance finiteLocalPrimeHomDiscrete : DiscreteTopology
    (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))) := ⟨rfl⟩
local instance finiteLocalPrimeHomContinuousSMul :
    @ContinuousSMul ℤ
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).hV2.toSMul
      inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩

/-- Continuous H1 of the actual local dual of the finite trace presentation. -/
abbrev RationalTraceFiniteLocalHomH1 :=
  ContinuousRepresentationH1 (rationalTraceFiniteLocalHomRep a q σ F hker p hp)
    (arithmeticPrimeRestrictedUnitHomAction_continuous a F
      (rationalTraceOriginalFiniteRep a q σ F hker) p hp)

variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The original finite local Hom H1 is identified with the actual prime
trace Hom H1 through the literal coefficient map. -/
def rationalTraceFiniteLocalHomH1Equiv :
    RationalTraceFiniteLocalHomH1 a q σ F hker p hp ≃+
      ContinuousRepresentationH1
        (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
        (rationalPrimeTraceUnitHomAction_continuous p hp q
          (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn) :=
  continuousH1AdditiveCoefficientEquiv _ _
    (rationalTraceFiniteLocalHomCoefficientEquiv a q σ F hker p hp)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalTraceFiniteLocalHomCoefficientEquiv_equivariant a q σ F hker p hp) _ _

/-- The finite local H1 equivalence preserves the literal transported cocycle. -/
theorem rationalTraceFiniteLocalHomH1Equiv_mk
    (c : continuousRepresentationCocyclesOne (rationalTraceFiniteLocalHomRep a q σ F hker p hp)) :
    rationalTraceFiniteLocalHomH1Equiv a q σ F hker p hp hσ hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv _ _
        (rationalTraceFiniteLocalHomCoefficientEquiv a q σ F hker p hp)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (rationalTraceFiniteLocalHomCoefficientEquiv_equivariant a q σ F hker p hp) c) := rfl

end
end Dubon2026
