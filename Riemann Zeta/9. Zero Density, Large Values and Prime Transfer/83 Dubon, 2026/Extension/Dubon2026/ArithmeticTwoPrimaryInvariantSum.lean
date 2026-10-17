import Dubon2026.ArithmeticTwoPrimaryCyclicCarry
import Dubon2026.ArithmeticTwoPrimaryCarryInvariantSum

/-! # The original two-primary arithmetic invariant sum is zero

Every original class with the given two-power annihilator has a proved
cyclic carry inside the retained cyclotomic field. Its actual finite and
real invariants therefore have finite support and total sum zero. This
discharges the two-primary rational unit-class sum in DUB-17's full-order
class chain; comparison with the coherent idele-class invariants remains separate.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators NumberField

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic

variable (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
include h2a

/-- Every original two-primary arithmetic unit class has finite support
of its actual prime invariants, whose sum plus its actual real invariant is zero. -/
theorem rationalArithmeticUnitInvariant_exists_two_primary_support_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
        originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
  have hc := rationalArithmeticUnitH2_exists_two_primary_cyclic_carry a r h2a x hx
  obtain ⟨k, F, E, hk, hcycl, hEF, hcyc, _, y, _, hy, d, hd, χ, q, hcarry⟩ := hc
  letI : Algebra ℚ E := E.toIntermediateField.algebra'
  letI : IsCyclic Gal(E/ℚ) := hcyc
  letI : IsCyclotomicExtension {2 ^ (k + 1)} ℚ F := hcycl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)⟩
  have hsum := @rationalTwoArithmeticCarry_exists_support_sum_zero a E hcyc
    _ _ d _ χ.toMonoidHom q _ _ F hEF k (by omega) hcycl
  have he : rationalArithmeticFiniteCarryClass a E χ.toMonoidHom q = x :=
    (congrArg (galoisUnitFiniteStageH2Inflation E) hcarry).trans hy
  simpa only [he] using hsum

/-- The total invariant vanishes on every finite support of the same
original two-primary class, retaining its real contribution. -/
theorem rationalArithmeticUnitInvariant_two_primary_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) (T : Finset Nat.Primes)
    (hT : ∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) :
    (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
  classical
  obtain ⟨S, hS, hsum⟩ :=
    rationalArithmeticUnitInvariant_exists_two_primary_support_sum_zero a r h2a x hx
  have hs : (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
      ∑ p ∈ S ∪ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
    Finset.sum_subset Finset.subset_union_left (fun p _ hp => hS p hp)
  have ht : (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
      ∑ p ∈ S ∪ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
    Finset.sum_subset Finset.subset_union_right (fun p _ hp => hT p hp)
  exact (congrArg (fun z => z + originalRealUnitH2Invariant
    (rationalArithmeticRealUnitH2Restriction a x)) (ht.trans hs.symm)).trans hsum

end
end Dubon2026
