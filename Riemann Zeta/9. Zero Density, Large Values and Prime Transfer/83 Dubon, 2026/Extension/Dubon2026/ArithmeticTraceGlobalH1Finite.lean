import Dubon2026.ArithmeticFiniteCoefficientH1
import Dubon2026.ArithmeticExceptionalLocalization

/-! Finiteness of the original two global trace H1 spaces.
Both original arithmetic actions are retained. This discharges global
finite-dimensionality for DUB-17's numerical Selmer comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)

include hqa ha

/-- The original arithmetic trace-zero H1 is finite by the actual finite-coefficient theorem. -/
theorem rationalArithmeticTraceH1_finite :
    Finite (ContinuousTraceZeroAdjointH1 σ hσ) := by
  haveI := rationalArithmeticFiniteCoefficientH1_finite a ha q hqa
    (matrixTraceZeroAdjointRep σ) (matrixTraceZeroAdjointAction_continuous σ hσ)
  exact Finite.of_injective (continuousTraceZeroH1GeneralEquiv σ hσ)
    (continuousTraceZeroH1GeneralEquiv σ hσ).injective

/-- The original cyclotomic-twisted global trace H1 is finite, including its genuine character. -/
theorem rationalArithmeticTraceDualH1_finite :
    Finite (RationalArithmeticTraceDualH1 a q hqa σ hσ) := by
  exact rationalArithmeticFiniteCoefficientH1_finite a ha q hqa
    (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
    (matrixTraceZeroCharacterAction_continuous σ hσ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)

end
end Dubon2026
