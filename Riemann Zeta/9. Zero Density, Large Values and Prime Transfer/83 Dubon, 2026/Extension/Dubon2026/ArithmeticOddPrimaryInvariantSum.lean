import Dubon2026.ArithmeticOddPrimaryCyclicCarry
import Dubon2026.ArithmeticPrincipalCharacterSupport
import Dubon2026.ArithmeticUnitPrimeInvariant
import Dubon2026.ArithmeticPrincipalCarryInvariant
import Dubon2026.GaloisUnitContinuousCorestriction

/-! # The actual rational odd-primary unit invariant sum is zero

Construct the faithful cyclic carry of the original arithmetic class,
then apply the actual rational principal-product character formula. It
supplies finite support and two-annihilation of the sum. The original
prime-power annihilator also kills the sum, so oddness forces zero. This
removes the Kummer/prime-torsion restriction on the rational reciprocity
input to DUB-17's full-order class and reverse-localization construction.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete

variable (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

include hq hq2 hqa

/-- Every actual odd-primary arithmetic unit class has finite prime-invariant support and zero total invariant. -/
theorem rationalArithmeticUnitPrimeInvariant_exists_support_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∉ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) ∧
      (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) = 0 := by
  classical
  have hcarryStage := rationalArithmeticUnitH2_exists_odd_primary_cyclic_carry a q r hq hq2 hqa x hx
  obtain ⟨k, F, _, hcycl, hcyc, y, _, hy, n, hn, χ, u, hcarry⟩ := hcarryStage
  let A₀ : Algebra ℚ F := F.toIntermediateField.algebra'
  have hcycl₀ : letI := A₀; IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcycl
  have hcyc₀ : letI := A₀; IsCyclic Gal(F/ℚ) := hcyc
  have hcyclAll : ∀ A : Algebra ℚ F, letI := A; IsCyclotomicExtension {q ^ (k + 1)} ℚ F := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact hcycl₀
  have hcycAll : ∀ A : Algebra ℚ F, letI := A; IsCyclic Gal(F/ℚ) := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact hcyc₀
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcyclAll _
  letI : IsCyclic Gal(F/ℚ) := hcycAll _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  obtain ⟨S, hS, htwo⟩ := rationalArithmeticPrincipalCharacter_exists_support_two_nsmul
    a F q hq hq2 k χ.toMonoidHom u
  have hlocal (p : Nat.Primes) : rationalArithmeticUnitPrimeInvariant a p.val p.property x =
      rationalCyclicInvariant n
        (χ.toMonoidHom (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd := by
    rw [← hy, ← hcarry]
    exact rationalArithmeticFiniteCarryInvariant a F p.val p.property χ.toMonoidHom u
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    exact (hlocal p).trans ((congrArg (rationalCyclicInvariant n) (hS p hp)).trans (map_zero _))
  · have hsum : (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
        rationalCyclicInvariant n (∑ p ∈ S,
          (χ.toMonoidHom (rationalArithmeticFiniteLocalReciprocityAut a F p.val p.property u)).toAdd) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun p _ => hlocal p)
    have htwoSum : 2 • (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) = 0 := by
      rw [hsum]
      have h := congrArg (rationalCyclicInvariant n) htwo
      simpa only [map_nsmul, map_zero] using h
    have hqSum : q ^ (r + 1) • (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) = 0 := by
      rw [Finset.smul_sum]
      apply Finset.sum_eq_zero
      intro p _
      rw [← map_nsmul, hx, map_zero]
    exact eq_zero_of_two_nsmul_eq_zero_of_odd_nsmul_eq_zero
      (q ^ (r + 1)) (hq.odd_of_ne_two hq2).pow _ htwoSum hqSum

/-- Any actual finite support of the same odd-primary prime invariants has zero sum. -/
theorem rationalArithmeticUnitPrimeInvariant_sum_zero
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) (T : Finset Nat.Primes)
    (hT : ∀ p ∉ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0) :
    (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) = 0 := by
  classical
  obtain ⟨S, hS, hsum⟩ := rationalArithmeticUnitPrimeInvariant_exists_support_sum_zero a q r hq hq2 hqa x hx
  have hs : (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
      ∑ p ∈ S ∪ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
    Finset.sum_subset Finset.subset_union_left (fun p _ hp => hS p hp)
  have ht : (∑ p ∈ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x) =
      ∑ p ∈ S ∪ T, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
    Finset.sum_subset Finset.subset_union_right (fun p _ hp => hT p hp)
  exact (ht.trans hs.symm).trans hsum

/-- The actual corestriction of an odd-primary class over any original finite
arithmetic subfield has finite rational prime support and zero invariant sum. -/
theorem rationalArithmeticUnitCorestriction_exists_support_sum_zero
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))] :
    letI : IsGalois F (rationalUnramifiedExtension a) :=
      IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension a)
    ∀ y : GaloisUnitContinuousH2 (K := F) (Ω := rationalUnramifiedExtension a),
      q ^ (r + 1) • y = 0 → ∃ S : Finset Nat.Primes,
        (∀ p ∉ S, rationalArithmeticUnitPrimeInvariant a p.val p.property
          (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F y) = 0) ∧
        (∑ p ∈ S, rationalArithmeticUnitPrimeInvariant a p.val p.property
          (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F y)) = 0 := by
  letI : IsGalois F (rationalUnramifiedExtension a) :=
    IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension a)
  intro y hy
  apply rationalArithmeticUnitPrimeInvariant_exists_support_sum_zero a q r hq hq2 hqa
    (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F y)
  rw [← map_nsmul, hy, map_zero]

end
end Dubon2026
