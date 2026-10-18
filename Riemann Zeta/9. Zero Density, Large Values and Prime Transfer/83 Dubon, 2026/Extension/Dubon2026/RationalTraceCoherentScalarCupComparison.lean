import Dubon2026.ArithmeticExceptionalTraceDuality
import Dubon2026.ArithmeticLocalNormalizationComparison

/-! Retain the coherent global-root normalization when using the original
local Cartier construction. The existing proved H2 coordinate comparison
supplies the exact factor, rather than identifying independently chosen
roots. This is required for DUB-17's exceptional-pairing annihilator test. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)
  (x : ContinuousRepresentationH1
    (matrixTraceZeroCharacterRep ρ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
    (matrixTraceZeroCharacterAction_continuous ρ hρ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous))
  (y : ContinuousTraceZeroAdjointH1 ρ hρ)

/-- The genuine coherent trace cup and independently normalized local
trace cup differ by the already constructed nonzero coordinate factor. -/
theorem rationalArithmeticPrimeTraceH1ScalarCup_comparison :
    rationalArithmeticPrimeTraceH1ScalarCup a q hqa p hp ρ hρ x y =
      rationalArithmeticLocalNormalizationScalar a q hqa p hp *
        rationalPrimeTraceH1ScalarCup p hp q ρ hρ x y :=
  rationalArithmeticLocalH2ScalarEquiv_comparison a q hqa p hp
    (matrixTraceZeroCharacterH1Cup ρ hρ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous x y)

/-- Scaling the actual local dual class by the derived coordinate factor
lets the original local Cartier construction realize the coherent pairing. -/
theorem rationalPrimeTraceH1ScalarCup_normalization_smul :
    rationalPrimeTraceH1ScalarCup p hp q ρ hρ
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp • x) y =
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p hp ρ hρ x y := by
  exact (LinearMap.congr_fun
    ((rationalPrimeTraceH1ScalarCup p hp q ρ hρ).map_smul
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp) x) y).trans
    (rationalArithmeticPrimeTraceH1ScalarCup_comparison a q hqa p hp ρ hρ x y).symm

end
end Dubon2026
