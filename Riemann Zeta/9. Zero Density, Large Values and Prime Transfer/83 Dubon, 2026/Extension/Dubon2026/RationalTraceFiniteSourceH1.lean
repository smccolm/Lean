import Dubon2026.RationalTraceOriginalLocalAction
import Dubon2026.ContinuousH1FinitePullback
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! Every finite trace-coefficient H1 class comes from the original
continuous arithmetic trace-zero H1. This is the source-entry obligation
for testing DUB-17's constructed Cartier relation on all finite classes. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois rationalTraceCompletionCoefficientTopology
  rationalTraceCompletionCoefficientDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- Integer scalars act continuously on the original discrete trace coefficient. -/
local instance traceFiniteSourceContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalArithmeticTraceZeroIntegerRep a q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)

/-- The descended finite coefficient inflates to the original arithmetic
coefficient by the literal identity on trace-zero matrices. -/
def rationalTraceFiniteSourceCoefficientMap :
    Rep.res (AlgEquiv.restrictNormalHom F)
      (rationalTraceOriginalFiniteRep a q σ F hker) ⟶ rationalArithmeticTraceZeroIntegerRep a q σ :=
  Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact finiteStageCoefficientRepresentation_apply (rationalArithmeticTraceZeroIntegerRep a q σ)
        F hker g x }

variable (hσ : Continuous σ)

/-- Native finite pullback constructs a continuous source class for every
finite H1 input, with its exact original algebraic cohomology image. -/
theorem rationalTraceFiniteStageH1_exists_source
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1) :
    ∃ x : ContinuousRepresentationH1 (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalTraceIntegerAction_continuous a q σ hσ),
      continuousH1ToAlgebraic (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ) x =
        groupCohomology.map (AlgEquiv.restrictNormalHom F)
          (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y :=
  continuousH1_exists_finite_pullback (AlgEquiv.restrictNormalHom F)
    (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField)
    (rationalTraceOriginalFiniteRep a q σ F hker) (rationalArithmeticTraceZeroIntegerRep a q σ)
    (rationalTraceIntegerAction_continuous a q σ hσ)
    (rationalTraceFiniteSourceCoefficientMap a q σ F hker) y

/-- The original trace-zero H1 retains its literal cocycles and boundaries
when its coefficient is viewed over the integers. -/
def rationalArithmeticTraceIntegerH1Equiv :
    ContinuousTraceZeroAdjointH1 σ hσ ≃+
      ContinuousRepresentationH1 (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ) :=
  (continuousTraceZeroH1GeneralEquiv σ hσ).toAddEquiv.trans
    (continuousH1AdditiveCoefficientEquiv (matrixTraceZeroAdjointRep σ)
      (rationalArithmeticTraceZeroIntegerRep a q σ) (AddEquiv.refl _)
      continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl) _ _)

/-- Every finite class is supplied by the original trace-zero continuous
source H1 tested in the scalar-cup annihilation condition. -/
theorem rationalTraceFiniteStageH1_exists_original_source
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1) :
    ∃ x : ContinuousTraceZeroAdjointH1 σ hσ,
      continuousH1ToAlgebraic (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ)
        (rationalArithmeticTraceIntegerH1Equiv a q σ hσ x) =
        groupCohomology.map (AlgEquiv.restrictNormalHom F)
          (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y := by
  obtain ⟨x, hx⟩ := rationalTraceFiniteStageH1_exists_source a q σ F hker hσ y
  refine ⟨(rationalArithmeticTraceIntegerH1Equiv a q σ hσ).symm x, ?_⟩
  rw [AddEquiv.apply_symm_apply]
  exact hx

end
end Dubon2026
