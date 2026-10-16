import Dubon2026.ArithmeticFiniteInvariantSumComparison
import Dubon2026.ArithmeticFiniteCarryInvariant
import Dubon2026.RationalCyclotomicPrincipalStageBridge

/-! # The original prime invariant on arithmetic unit cohomology

Compose the existing literal arithmetic restriction and normalized local
invariant. The map agrees with the existing Kummer invariant. This keeps the actual coefficient and
completion maps in DUB-17's odd-primary reciprocity generalization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete
  arithmeticGlobalUnitContinuousSMul arithmeticPrimeInvariantUnitTopology
  arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The literal arithmetic prime restriction followed by the original normalized local invariant. -/
def rationalArithmeticUnitPrimeInvariant (p : ℕ) (hp : p.Prime) :
    GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)).toLinearMap.comp (rationalArithmeticUnitH2Restriction a p hp)

/-- The same original normalized map gives the existing arithmetic Kummer invariant. -/
theorem rationalArithmeticUnitPrimeInvariant_kummer
    (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
    [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
    (p : ℕ) (hp : p.Prime)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticUnitPrimeInvariant a p hp
      (rationalArithmeticKummerH2Inclusion a q (rationalArithmeticCyclotomicH2RootEquiv a q hqa x)) =
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p hp x := rfl

end
end Dubon2026
