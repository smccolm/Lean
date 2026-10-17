import Dubon2026.ArithmeticTwoPrimaryInvariantSum
import Dubon2026.ArithmeticOddPrimaryInvariantSum

/-! # Original rational unit reciprocity for every prime-power class

The proved two-primary theorem includes the actual real invariant. For
odd primes the existing finite sum vanishes and the real invariant is
killed by both two and the original odd annihilator. These give the same
finite-plus-real statement for every coefficient prime in the original
ramification parameter. DUB-17 still needs its coherent full-idele comparison.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators NumberField

attribute [local instance] originalRealPeriodQuadratic
variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]

private theorem realUnitInvariant_two_nsmul
    (x : GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ)) :
    2 • originalRealUnitH2Invariant x = 0 := by
  let z := originalIntegerSignIndex (originalRealComplexH2SignEquiv x)
  have hz : 2 • z = 0 := by
    simpa only [← ZMod.natCast_self 2, Nat.cast_smul_eq_nsmul] using zero_smul (ZMod 2) z
  change 2 • rationalCyclicInvariant 2 z = 0
  rw [← map_nsmul, hz, map_zero]

private theorem realUnitInvariant_eq_zero_of_odd_annihilator
    (m : ℕ) (hm : Odd m) (x : GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ))
    (hx : m • x = 0) : originalRealUnitH2Invariant x = 0 := by
  apply eq_zero_of_two_nsmul_eq_zero_of_odd_nsmul_eq_zero m hm _ (realUnitInvariant_two_nsmul x)
  rw [← map_nsmul, hx, map_zero]

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul

variable (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include hq hqa

/-- Every actual rational arithmetic unit-H2 prime-power class has finite
prime-invariant support and zero total including its actual real invariant. -/
theorem rationalArithmeticUnitInvariant_exists_prime_power_support_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    ∃ T : Finset Nat.Primes,
      (∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
        originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
  by_cases htwo : q = 2
  · subst q
    exact rationalArithmeticUnitInvariant_exists_two_primary_support_sum_zero a r hqa x hx
  · obtain ⟨T, hT, hs⟩ :=
      rationalArithmeticUnitPrimeInvariant_exists_support_sum_zero a q r hq htwo hqa x hx
    have hreal : originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
      apply realUnitInvariant_eq_zero_of_odd_annihilator (q ^ (r + 1)) (hq.odd_of_ne_two htwo).pow
      exact (map_nsmul (rationalArithmeticRealUnitH2Restriction a) (q ^ (r + 1)) x).symm.trans
        ((congrArg (rationalArithmeticRealUnitH2Restriction a) hx).trans (map_zero _))
    exact ⟨T, hT, (congrArg₂ (fun u v : AddCircle (1 : ℚ) => u + v) hs hreal).trans (zero_add 0)⟩

/-- The same finite-plus-real prime-power invariant sum vanishes on any
finite support of the original arithmetic class. -/
theorem rationalArithmeticUnitInvariant_prime_power_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) (T : Finset Nat.Primes)
    (hT : ∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) :
    (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a x) = 0 := by
  classical
  obtain ⟨S, hS, hsum⟩ :=
    rationalArithmeticUnitInvariant_exists_prime_power_support_sum_zero a q r hq hqa x hx
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
