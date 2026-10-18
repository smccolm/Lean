import Dubon2026.RationalTraceFiniteSourceH1

/-! The actual source trace-zero cocycle in the original integer coefficient.
Its unchanged representative connects the source H1 preimage to the finite
local lift in DUB-17's Cartier total comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module
attribute [local instance] rationalTraceCompletionCoefficientTopology
  rationalTraceCompletionCoefficientDiscrete traceFiniteSourceContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- View the original continuous source cocycle over the integers using
the existing additive coefficient equivalence. -/
def rationalTraceSourceIntegerCocycle (c : continuousTraceZeroAdjointCocycles σ) :
    continuousRepresentationCocyclesOne (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  continuousCocycleOneAdditiveEquiv (matrixTraceZeroAdjointRep σ)
    (rationalArithmeticTraceZeroIntegerRep a q σ) (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl)
    ⟨c.val, c.property⟩

/-- No original source matrix value changes. -/
theorem rationalTraceSourceIntegerCocycle_apply (c : continuousTraceZeroAdjointCocycles σ)
    (g : rationalArithmeticGaloisGroup a) :
    (rationalTraceSourceIntegerCocycle a q σ c).val g = c.val g := rfl

/-- The constructed representative gives precisely the original integer H1 class. -/
theorem rationalTraceSourceIntegerCocycle_class (hσ : Continuous σ)
    (c : continuousTraceZeroAdjointCocycles σ) :
    rationalArithmeticTraceIntegerH1Equiv a q σ hσ (Quotient.mk _ c) =
      Quotient.mk _ (rationalTraceSourceIntegerCocycle a q σ c) := rfl

end
end Dubon2026
