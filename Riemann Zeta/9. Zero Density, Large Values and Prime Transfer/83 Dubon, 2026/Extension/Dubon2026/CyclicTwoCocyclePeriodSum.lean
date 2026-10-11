import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Exact cyclic period sums of the original unnormalized two-cocycles -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

private theorem cyclicPowerSum_shift {G V : Type*} [Group G] [AddCommGroup V]
    (g : G) (n : ℕ) (hn : g ^ n = 1) (f : G → V) :
    ∑ i ∈ Finset.range n, f (g ^ (i + 1)) = ∑ i ∈ Finset.range n, f (g ^ i) := by
  have h := (Finset.sum_range_succ' (fun i => f (g ^ i)) n).symm.trans
    (Finset.sum_range_succ (fun i => f (g ^ i)) n)
  simp only [pow_zero, hn] at h
  exact add_right_cancel h

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (g : G) (n : ℕ)

/-- The literal sum of original two-cochain values along one generator period. -/
def representationCyclicTwoCochainPeriodSum : (G × G → A) →ₗ[R] A where
  toFun c := ∑ i ∈ Finset.range n, c (g ^ i, g)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum]

/-- The original unnormalized cocycle identity makes the actual period sum
invariant under the original generator action. No normalization at one is assumed. -/
theorem representationCyclicTwoCocyclePeriodSum_fixed (hn : g ^ n = 1)
    (c : groupCohomology.cocycles₂ A) :
    A.ρ g (representationCyclicTwoCochainPeriodSum A g n c) =
      representationCyclicTwoCochainPeriodSum A g n c := by
  have h : (∑ i ∈ Finset.range n, (c (g * g ^ i, g) + c (g, g ^ i))) =
      ∑ i ∈ Finset.range n, (A.ρ g (c (g ^ i, g)) + c (g, g ^ i * g)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (groupCohomology.mem_cocycles₂_iff c).mp c.property g (g ^ i) g
  simp_rw [← pow_succ', ← pow_succ] at h
  have hleft : (∑ i ∈ Finset.range n, c (g ^ (i + 1), g)) =
      ∑ i ∈ Finset.range n, c (g ^ i, g) :=
    cyclicPowerSum_shift g n hn (fun x => c (x, g))
  have hright : (∑ i ∈ Finset.range n, c (g, g ^ (i + 1))) =
      ∑ i ∈ Finset.range n, c (g, g ^ i) :=
    cyclicPowerSum_shift g n hn (fun x => c (g, x))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← map_sum (A.ρ g), hleft, hright] at h
  exact (add_right_cancel h).symm

/-- The original coboundary period sum is the literal action-norm sum
of the original cochain value at the generator. -/
theorem representationCyclicTwoCochainPeriodSum_coboundary (hn : g ^ n = 1)
    (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g n (groupCohomology.d₁₂ A b) =
      ∑ i ∈ Finset.range n, A.ρ (g ^ i) (b g) := by
  change (∑ i ∈ Finset.range n,
    (A.ρ (g ^ i) (b g) - b (g ^ i * g) + b (g ^ i))) = _
  simp_rw [← pow_succ]
  have hb : (∑ i ∈ Finset.range n, b (g ^ (i + 1))) =
      ∑ i ∈ Finset.range n, b (g ^ i) := cyclicPowerSum_shift g n hn b
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hb]
  abel

end
end Dubon2026
