import Dubon2026.ArithmeticFiniteSUnitDualConnecting
import Dubon2026.RationalTraceFiniteTowerAction
import Dubon2026.ArithmeticTraceSUnitCohomology

/-! Apply the native finite S-unit connecting class and the original
trace/Cartier H1 equivalence to the actual descended trace coefficient.
This constructs an original global trace-dual class from the finite
correction; identifying its prescribed local restrictions remains the
next DUB-17 reverse-localization obligation. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois

local instance rationalTraceFiniteDualClassAlgebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

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

/-- The actual finite-restriction S-unit Hom coefficient. -/
abbrev rationalTraceFiniteSUnitHomRep :=
  (Rep.ihom (Rep.res (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ))
    (rationalTraceOriginalFiniteRep a q σ F hker))).obj
      (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha)

/-- The coefficient identification preserves the literal linear function. -/
def rationalTraceFiniteSUnitHomCoefficientEquiv :
    rationalTraceFiniteSUnitHomRep a ha q σ F hker ≃+
      rationalArithmeticTraceSUnitHomRep a ha q σ := AddEquiv.refl _

/-- The coefficient identification intertwines the actual finite-stage
restriction action and the original arithmetic trace Hom action. -/
theorem rationalTraceFiniteSUnitHomCoefficientEquiv_equivariant
    (g : rationalArithmeticGaloisGroup a)
    (f : rationalTraceFiniteSUnitHomRep a ha q σ F hker) :
    rationalTraceFiniteSUnitHomCoefficientEquiv a ha q σ F hker
      ((rationalTraceFiniteSUnitHomRep a ha q σ F hker).ρ g f) =
      (rationalArithmeticTraceSUnitHomRep a ha q σ).ρ g
        (rationalTraceFiniteSUnitHomCoefficientEquiv a ha q σ F hker f) := by
  apply LinearMap.ext
  intro x
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let f' : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ] D := f
  change D.ρ g (f' (finiteStageCoefficientRepresentation
    (rationalArithmeticTraceZeroIntegerRep a q σ) F hker
      (AlgEquiv.restrictNormalHom F g⁻¹) x)) =
    D.ρ g (f' ((rationalArithmeticTraceZeroIntegerRep a q σ).ρ g⁻¹ x))
  exact congrArg (fun z => D.ρ g (f' z))
    (finiteStageCoefficientRepresentation_apply
      (rationalArithmeticTraceZeroIntegerRep a q σ) F hker g⁻¹ x)

/-- Continuous H1 of the literal global restriction of the finite trace
coefficient with its actual arithmetic S-unit Hom target. -/
abbrev RationalTraceFiniteSUnitHomH1 :=
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let C := Rep.res π B
  letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  letI : Finite C := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let A := (Rep.ihom C).obj D
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : @ContinuousSMul ℤ C C.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ C C.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ (AlgebraicClosure ℚ) a F B
  let hD := originalArithmeticSUnitAction_continuous ℚ (AlgebraicClosure ℚ) a ha
  let hA := originalInternalHomAction_continuous_of_finite C D hC hD
  ContinuousRepresentationH1 A hA

/-- The finite trace S-unit Hom H1 is identified with the original
global trace-dual H1, through the proved native Cartier equivalence. -/
def rationalTraceFiniteSUnitHomH1Equiv :
    RationalTraceFiniteSUnitHomH1 a ha q σ F hker ≃+
      RationalArithmeticTraceDualH1 a q hqa σ hσ := by
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let C := Rep.res π B
  letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  letI : Finite C := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  let D := originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha
  let A := (Rep.ihom C).obj D
  let T := rationalArithmeticTraceSUnitHomRep a ha q σ
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace T := ⊥
  letI : DiscreteTopology T := ⟨rfl⟩
  letI : @ContinuousSMul ℤ C C.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ C C.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ D D.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D D.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ A A.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ A A.hV2.toSMul _ _ continuous_of_discreteTopology
  letI : @ContinuousSMul ℤ T T.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ T T.hV2.toSMul _ _ continuous_of_discreteTopology
  let hC := arithmeticFiniteStageRepresentationAction_continuous ℚ (AlgebraicClosure ℚ) a F B
  let hD := originalArithmeticSUnitAction_continuous ℚ (AlgebraicClosure ℚ) a ha
  let hA := originalInternalHomAction_continuous_of_finite C D hC hD
  let hT := rationalArithmeticTraceSUnitHomAction_continuous a ha q σ hσ hqa hn
  let e : A ≃+ T := rationalTraceFiniteSUnitHomCoefficientEquiv a ha q σ F hker
  have he := rationalTraceFiniteSUnitHomCoefficientEquiv_equivariant a ha q σ F hker
  exact (continuousH1AdditiveCoefficientEquiv A T e continuous_of_discreteTopology
    continuous_of_discreteTopology he hA hT).trans
      (rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn).symm

/-- The actual original global trace-dual H1 class associated with a finite
S-unit relation, through the proved arithmetic connecting construction. -/
def rationalTraceFiniteSUnitDualClass
    (η : originalRelationModule (rationalTraceOriginalFiniteRep a q σ F hker) ⟶
      arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    RationalArithmeticTraceDualH1 a q hqa σ hσ := by
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  letI : Finite B := inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))
  have hB (b : B) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  let c : RationalTraceFiniteSUnitHomH1 a ha q σ F hker :=
    arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa F B hB η
  exact rationalTraceFiniteSUnitHomH1Equiv a ha q σ F hker hσ hqa hn c

end
end Dubon2026
