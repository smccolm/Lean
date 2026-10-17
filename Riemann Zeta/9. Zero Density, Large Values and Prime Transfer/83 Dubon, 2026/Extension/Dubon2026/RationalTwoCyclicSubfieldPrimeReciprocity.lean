import Dubon2026.RationalTwoCyclotomicPrimeNorm
import Dubon2026.LocalFieldCyclicSubfieldNormKernel

/-! # Prime-two cancellation on the actual cyclic cyclotomic subfield

The original cyclotomic norm witness descends through the literal field
norm tower. The actual local reciprocity map therefore kills the prime
factor on every cyclic subfield. This removes that cancellation input
from DUB-17's remaining conductor-two principal-product calculation.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- The original prime-two unit acts trivially under local reciprocity
on a cyclic subfield of the constructed cyclotomic closure stage. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_prime
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
      (Additive.ofMul (rationalPrimePrimeUnit 2 Nat.prime_two))).toMul = 1 := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  exact localFieldFiniteCyclicReciprocity_eq_one_of_overfield_norm K Ω L F hL
    (rationalPrimePrimeUnit 2 Nat.prime_two)
    (rationalTwoOriginalCyclotomicClosure_exists_prime_norm n a hn u hu ha)

end
end Dubon2026
