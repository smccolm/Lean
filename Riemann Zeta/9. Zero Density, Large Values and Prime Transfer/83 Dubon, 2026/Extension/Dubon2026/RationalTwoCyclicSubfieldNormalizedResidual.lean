import Dubon2026.RationalTwoCyclicSubfieldPrimeCancellation
import Dubon2026.RationalPrimeNormalizedResidual

/-! # Removing the rational two-power in the original cyclic reciprocity map

The already proved norm-two witness kills every integral power of two.
Thus the normalized residual has exactly the original rational unit's
reciprocity value on the same cyclic subfield. This removes the order-zero
restriction at the source entry to DUB-17's principal-product calculation.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]

include hn hL

/-- Removing the exact normalized two-power preserves the original
cyclic-subfield reciprocity value of every rational unit. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_normalizedResidual
    (q : ℚˣ) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ρ := localFieldFiniteCyclicReciprocity K Ω L
    ρ (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two
        (rationalPrimeNormalizedResidual 2 Nat.prime_two q))) =
      ρ (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q)) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  let qK := rationalPrimeRationalUnit 2 Nat.prime_two q
  let π := rationalPrimePrimeUnit 2 Nat.prime_two
  let z := localFieldUnitOrder K (Additive.ofMul qK)
  have hπzero : ρ (Additive.ofMul π) = 0 := by
    apply Additive.toMul.injective
    exact rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_prime n c hn v hv hc L hL
  rw [rationalPrimeRationalUnit_normalizedResidual]
  change ρ (Additive.ofMul qK - z • Additive.ofMul π) = ρ (Additive.ofMul qK)
  rw [map_sub, map_zsmul, hπzero, zsmul_zero, sub_zero]

end
end Dubon2026
