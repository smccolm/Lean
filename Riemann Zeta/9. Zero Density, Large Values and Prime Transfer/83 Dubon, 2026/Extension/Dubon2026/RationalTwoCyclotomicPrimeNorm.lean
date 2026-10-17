import Dubon2026.RationalPrimeOriginalCyclotomicNorm

/-! # The prime two is a norm at the constructed cyclotomic levels

The pinned primitive-root norm theorem already covers the prime two once
the conductor exponent is at least two. The constructed splitting field
has a stronger bound. This gives the prime-cancellation input for the
conductor-two reciprocity formula serving DUB-17's full-order class route.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime rationalPrimeWittOriginalAlgebra
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- At the required two-power levels, the original root minus one has
norm two. The lower bound excludes the exceptional second-root level. -/
theorem rationalTwoOriginalCyclotomicStageRoot_norm_sub_one
    (n : ℕ) (hn : 1 ≤ n) :
    Algebra.norm (rationalPrimeLocalField 2 Nat.prime_two)
        (rationalPrimeOriginalCyclotomicStageRoot 2 Nat.prime_two n - 1) =
      (2 : rationalPrimeLocalField 2 Nat.prime_two) := by
  letI : IsCyclotomicExtension {2 ^ (n + 1)} (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeOriginalCyclotomicStage 2 Nat.prime_two n) :=
    rationalPrimeOriginalCyclotomicStage_isCyclotomic 2 Nat.prime_two n
  exact (rationalPrimeOriginalCyclotomicStageRoot_isPrimitive 2 Nat.prime_two n).norm_sub_one_two
    (by omega) (rationalPrimePowerCyclotomic_irreducible 2 Nat.prime_two n)

/-- The norm-two formula transports to the same closure stage used by
the changed-uniformizer reciprocity calculation. -/
theorem rationalTwoOriginalCyclotomicClosureRoot_norm_sub_one
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a) :
    Algebra.norm (rationalPrimeLocalField 2 Nat.prime_two)
        (rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha - 1) =
      (2 : rationalPrimeLocalField 2 Nat.prime_two) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let L₀ := rationalPrimeOriginalCyclotomicStage 2 Nat.prime_two n
  let L := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
  let e : L₀ ≃ₐ[K] L := rationalPrimeOriginalCyclotomicClosureEquiv 2 Nat.prime_two n a u hu ha
  calc
    Algebra.norm K (rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha - 1) =
        Algebra.norm K (e (rationalPrimeOriginalCyclotomicStageRoot 2 Nat.prime_two n - 1)) := by
      congr 1
      simp only [e, rationalPrimeOriginalCyclotomicClosureRoot, map_sub, map_one]
    _ = Algebra.norm K (rationalPrimeOriginalCyclotomicStageRoot 2 Nat.prime_two n - 1) :=
      Algebra.norm_eq_of_algEquiv e _
    _ = (2 : K) := rationalTwoOriginalCyclotomicStageRoot_norm_sub_one n hn

/-- The original prime-two unit is an actual unit norm from the same
two-power cyclotomic closure field. -/
theorem rationalTwoOriginalCyclotomicClosure_exists_prime_norm
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let L := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = rationalPrimePrimeUnit 2 Nat.prime_two := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let L := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
  have hnorm : Algebra.norm K (ζ - 1) = (2 : K) :=
    rationalTwoOriginalCyclotomicClosureRoot_norm_sub_one n a hn u hu ha
  have hne : ζ - 1 ≠ 0 := by
    intro hzero
    have hz : (0 : K) = 2 := by simpa only [hzero, Algebra.norm_zero] using hnorm
    exact (rationalPrimePrimeUnit 2 Nat.prime_two).ne_zero hz.symm
  refine ⟨Units.mk0 (ζ - 1) hne, ?_⟩
  apply Units.ext
  exact hnorm

end
end Dubon2026
