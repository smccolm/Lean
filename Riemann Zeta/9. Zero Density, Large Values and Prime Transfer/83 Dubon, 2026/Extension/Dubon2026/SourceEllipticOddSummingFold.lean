import Dubon2026.SourceEllipticOddSummingStructure

/-! Reindexing the actual odd cyclic subgroup for its quotient
discriminant. This supplies the doubling permutation and orbit-trace identities
used to prove the odd quotient elliptic, then the prime quotient products and
inertia census required by DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing coordinate injectivity
supplies finite sums and products; no cardinality or permutation is assumed. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}
theorem sum_oddOrderSummingSet_eq (hQ : addOrderOf Q = 2 * n + 1)
    {M : Type*} [AddCommMonoid M] (g : F × F → M) :
    ∑ P ∈ oddOrderSummingSet V Q n, g P
      = ∑ k ∈ Finset.Icc 1 n, g ((coordsOrZero (k • Q))) := by
  rw [oddOrderSummingSet, Finset.sum_image (fun k hk k' hk' h =>
    coordsOrZero_odd_nsmul_injOn hQ (by simpa using hk) (by simpa using hk') h)]

theorem prod_oddOrderSummingSet_eq (hQ : addOrderOf Q = 2 * n + 1)
    {M : Type*} [CommMonoid M] (g : F × F → M) :
    ∏ P ∈ oddOrderSummingSet V Q n, g P
      = ∏ k ∈ Finset.Icc 1 n, g ((coordsOrZero (k • Q))) := by
  rw [oddOrderSummingSet, Finset.prod_image (fun k hk k' hk' h =>
    coordsOrZero_odd_nsmul_injOn hQ (by simpa using hk) (by simpa using hk') h)]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
