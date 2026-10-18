import Dubon2026.RationalTraceFiniteSourceH1
/-! Construct one original source cocycle for each finite H1 class, so its restrictions at every exceptional prime use the same representative in DUB-17's total-vanishing test. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module
attribute [local instance] rationalTraceCompletionCoefficientTopology
  rationalTraceCompletionCoefficientDiscrete traceFiniteSourceContinuousSMul
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))


/-- A single original continuous source cocycle supplies the finite H1
class and hence all of its local restrictions simultaneously. -/
theorem rationalTraceFiniteStageH1_exists_original_cocycle
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hker : ∀ u : rationalArithmeticGaloisGroup a,
      AlgEquiv.restrictNormalHom F u = 1 →
      ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
        (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
    (hσ : Continuous σ)
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1) :
    ∃ c : continuousTraceZeroAdjointCocycles σ,
      continuousH1ToAlgebraic (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ)
        (rationalArithmeticTraceIntegerH1Equiv a q σ hσ (Quotient.mk _ c)) =
        groupCohomology.map (AlgEquiv.restrictNormalHom F)
          (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y := by
  obtain ⟨x, hx⟩ := rationalTraceFiniteStageH1_exists_original_source a q σ F hker hσ y
  obtain ⟨c, rfl⟩ := Quotient.exists_rep x
  exact ⟨c, hx⟩

end
end Dubon2026
