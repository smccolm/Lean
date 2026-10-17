import Dubon2026.RationalTwoCyclicSubfieldPrimeReciprocity
import Dubon2026.RationalPrimeChangedCyclotomicClosureNaturalUnitAction

/-! # Cancel the prime factor on the actual two-primary cyclic subfield

The proved prime-two norm and original reciprocity homomorphism remove
the prime factor from the changed-uniformizer value. This supplies the
natural-unit step toward DUB-17's conductor-two principal-product formula.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- On the same cyclic subfield, the original reciprocity of `a * 2`
equals the original reciprocity of the natural unit `a`. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_mul_prime_eq_natural
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)] :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit 2 Nat.prime_two a ha))).toMul =
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  have hpzero : (ρ (Additive.ofMul (rationalPrimePrimeUnit 2 Nat.prime_two))).toMul = 1 :=
    rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_prime n a hn u hu ha L hL
  have hpzero' : ρ (Additive.ofMul (rationalPrimePrimeUnit 2 Nat.prime_two)) = 0 := by
    simpa using congrArg Multiplicative.toAdd hpzero
  have hadd : ρ (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit 2 Nat.prime_two a ha)) =
      ρ (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha)) := by
    rw [← rationalPrimeNaturalUnit_mul_prime 2 Nat.prime_two a ha]
    change ρ (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha) +
        Additive.ofMul (rationalPrimePrimeUnit 2 Nat.prime_two)) =
      ρ (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))
    rw [map_add, hpzero', add_zero]
  exact congrArg Additive.toMul hadd

end
end Dubon2026
