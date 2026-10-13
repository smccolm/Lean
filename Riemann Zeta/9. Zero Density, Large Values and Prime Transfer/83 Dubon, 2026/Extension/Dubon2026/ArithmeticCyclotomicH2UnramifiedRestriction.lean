import Dubon2026.ArithmeticH2UnramifiedRestriction
import Dubon2026.ArithmeticCyclotomicH2FiniteStage

/-! # The original arithmetic cyclotomic H2 vanishes locally away from S

Finite descent constructs the arithmetic stage for the actual original class.
Its actual local compositum is unramified, and the proved field and cohomology
squares transfer absolute inflation vanishing to the original cyclotomic
restriction. This discharges the local vanishing input to DUB-17 finite support.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra arithmeticFiniteStageH2Galois

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

/-- Every original arithmetic cyclotomic H2 class restricts to zero at an
actual prime away from the exceptional integer. The finite-stage presentation,
local unramifiedness and original coefficient comparison are all derived. -/
theorem rationalPrimeCyclotomicH2Restriction_eq_zero (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalPrimeCyclotomicH2Restriction a q hqa p hp x = 0 := by
  let A := coefficientCharacterRep
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
  have hA := coefficientCharacterAction_continuous _
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
  have hx : continuousRepresentationH2Restriction A hA
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous x = 0 := by
    exact arithmeticH2Restriction_eq_zero a p hp q A hA ha hpa x
  let e := continuousH2CoefficientCongr
    (rationalArithmeticCyclotomicRepresentation_restriction a q hqa p hp (k := ZMod q))
    (restrictedCoefficientAction_continuous A
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous hA)
    (coefficientCharacterAction_continuous _
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)
  exact (congrArg e hx).trans e.map_zero

end
end Dubon2026
