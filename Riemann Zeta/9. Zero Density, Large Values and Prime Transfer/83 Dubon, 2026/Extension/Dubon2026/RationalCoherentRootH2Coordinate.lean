import Dubon2026.RationalCoherentRootCoordinate
import Dubon2026.ArithmeticExceptionalTraceDuality

/-! Identify the proved H2 normalization factor with the literal root
coordinate. This keeps DUB-17's scaled Cartier cocycle compatible with
the actual global-root coefficient map used by the S-unit diagonal. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete characterDualSequenceContinuousSMul
  rationalPrimeLocalField_charZero

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  (x : ContinuousRepresentationH2 (coefficientCharacterRep
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
    (coefficientCharacterAction_continuous _
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous))

/-- The actual coherent root H2 map is the original local root map after
scalar multiplication by the literal root coordinate. -/
theorem rationalArithmeticLocalCyclotomicH2RootEquiv_coordinate :
    rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp x =
      rationalPrimeCyclotomicH2RootEquiv p hp q
        (rationalArithmeticLocalRootCoordinate a q hqa p hp • x) := by
  induction x using Quotient.inductionOn' with
  | h c =>
    apply congrArg ((continuousRepresentationCoboundariesTwo
      (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q)
      (discreteGaloisRootAction_continuous (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q)).mkQ)
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact rationalArithmeticLocalRootCoefficientEquiv_coordinate a q hqa p hp (c.val z)

/-- The coherent scalar H2 coordinate is multiplied by the literal root
coordinate under the unchanged original local invariant. -/
theorem rationalArithmeticLocalH2ScalarEquiv_root_coordinate :
    rationalArithmeticLocalH2ScalarEquiv a q hqa p hp x =
      rationalArithmeticLocalRootCoordinate a q hqa p hp *
        rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x := by
  exact (congrArg (rationalPrimeRootH2CyclicEquiv p hp q)
    (rationalArithmeticLocalCyclotomicH2RootEquiv_coordinate a q hqa p hp x)).trans
    ((rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).map_smul
      (rationalArithmeticLocalRootCoordinate a q hqa p hp) x)

omit x in
/-- The previously constructed invariant normalization factor is exactly
the actual coefficient/root factor, so the same scaling serves both maps. -/
theorem rationalArithmeticLocalNormalizationScalar_eq_rootCoordinate :
    rationalArithmeticLocalNormalizationScalar a q hqa p hp =
      rationalArithmeticLocalRootCoordinate a q hqa p hp := by
  unfold rationalArithmeticLocalNormalizationScalar
  rw [rationalArithmeticLocalH2ScalarEquiv_root_coordinate,
    LinearEquiv.apply_symm_apply, mul_one]

omit x in
/-- Literal compatibility of the coherent coefficient map with the
normalization scalar used to construct the actual Cartier family. -/
theorem rationalArithmeticLocalRootCoefficientEquiv_normalization (z : ZMod q) :
    rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp z =
      rationalPrimeCyclotomicRootCoefficientEquiv p hp q
        (rationalArithmeticLocalNormalizationScalar a q hqa p hp * z) := by
  rw [rationalArithmeticLocalNormalizationScalar_eq_rootCoordinate]
  exact rationalArithmeticLocalRootCoefficientEquiv_coordinate a q hqa p hp z

end
end Dubon2026
