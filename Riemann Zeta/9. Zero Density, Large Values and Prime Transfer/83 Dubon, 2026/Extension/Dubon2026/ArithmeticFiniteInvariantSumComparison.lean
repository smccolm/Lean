import Dubon2026.ArithmeticFiniteInvariantSum

/-! # The original finite-prime sum equals the original unit-H2 invariant sum

The global primitive root and its actual local images determine the same
normalization on every term. This is the exact consumer needed to connect a
proved global reciprocity theorem to the DUB-17 arithmetic coefficient sum.
The zero value of the sum remains unproved here.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticPrimeInvariantRootTopology arithmeticPrimeInvariantRootDiscrete
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The actual local unit invariant of the same original arithmetic Kummer class. -/
def rationalArithmeticKummerUnitPrimeInvariant (p : ℕ) (hp : p.Prime)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) : AddCircle (1 : ℚ) :=
  localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)
    (rationalArithmeticUnitH2Restriction a p hp
      (rationalArithmeticKummerH2Inclusion a q
        (rationalArithmeticCyclotomicH2RootEquiv a q hqa x)))

/-- The coherent original scalar is the original local unit invariant. -/
theorem rationalArithmeticPrimeH2Invariant_unit_invariant (p : ℕ) (hp : p.Prime)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticPrimeH2Invariant a q hqa p hp x) =
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p hp x := by
  change rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
    (rationalPrimeCyclotomicH2Restriction a q hqa p hp x)) = _
  exact rationalArithmeticLocalH2ScalarEquiv_global_invariant a q hqa p hp x

include ha

/-- The original unit-H2 invariants of a global Kummer image have proved finite support. -/
theorem rationalArithmeticKummerUnitInvariant_finite_support
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    (Function.support (fun p : Nat.Primes =>
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x)).Finite := by
  apply (rationalArithmeticPrimeH2Invariant_finite_support a q hqa ha x).subset
  intro p hp
  change rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x ≠ 0
  intro hz
  apply hp
  exact (rationalArithmeticPrimeH2Invariant_unit_invariant a q hqa p.val p.property x).symm.trans
    ((congrArg (rationalCyclicInvariant q) hz).trans (map_zero _))

/-- The coherent scalar sum maps to the sum of the actual original local unit invariants,
term for term, over its proved support. No reciprocity premise is introduced. -/
theorem rationalArithmeticFiniteH2InvariantSum_unit_invariants
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x := by
  rw [rationalArithmeticFiniteH2InvariantSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact rationalArithmeticPrimeH2Invariant_unit_invariant a q hqa p.val p.property x

end
end Dubon2026
