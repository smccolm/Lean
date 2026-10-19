import Dubon2026.RationalTraceFiniteSUnitDualClass

/-! Recover the literal S-unit Hom cocycle of the constructed original
global trace-dual class. This is the finite/global coefficient comparison
needed to localize the actual class in DUB-17's reverse-localization proof. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

attribute [local instance] rationalTraceFiniteDualClassAlgebraicClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)


/-- The actual finite global S-unit Hom uses the original discrete topology. -/
local instance finiteGlobalTraceHomTopology :
    TopologicalSpace (rationalTraceFiniteSUnitHomRep a ha q σ F hker) := ⊥
local instance finiteGlobalTraceHomDiscrete :
    DiscreteTopology (rationalTraceFiniteSUnitHomRep a ha q σ F hker) := ⟨rfl⟩
local instance finiteGlobalTraceHomContinuousSMul :
    @ContinuousSMul ℤ (rationalTraceFiniteSUnitHomRep a ha q σ F hker)
      (rationalTraceFiniteSUnitHomRep a ha q σ F hker).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- Retain the discrete topology of the original global trace S-unit Hom. -/
local instance originalGlobalTraceHomTopology :
    TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ) := ⊥
local instance originalGlobalTraceHomDiscrete :
    DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ) := ⟨rfl⟩
local instance originalGlobalTraceHomContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticTraceSUnitHomRep a ha q σ)
      (rationalArithmeticTraceSUnitHomRep a ha q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Passing the finite S-unit Hom class through the original trace-dual
identification and back retains the literal coefficient cocycle. -/
theorem rationalTraceFiniteSUnitHomH1Equiv_toHom_mk
    (c : continuousRepresentationCocyclesOne (rationalTraceFiniteSUnitHomRep a ha q σ F hker)) :
    rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn
      (rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn (Submodule.Quotient.mk c)) =
    Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv _ _
      (rationalTraceFiniteSUnitHomCoefficientEquiv a ha q σ F hker)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (rationalTraceFiniteSUnitHomCoefficientEquiv_equivariant a ha q σ F hker) c) := by
  simp only [rationalTraceFiniteSUnitHomH1Equiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, continuousH1AdditiveCoefficientEquiv_mk]
  rfl

end
end Dubon2026
