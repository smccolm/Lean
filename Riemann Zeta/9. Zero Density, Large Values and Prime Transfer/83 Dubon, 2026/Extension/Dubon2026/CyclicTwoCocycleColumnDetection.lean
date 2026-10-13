import Dubon2026.CyclicTwoCocyclePeriodSum
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # The actual generator column determines a finite cyclic two-cocycle

The cocycle identity propagates equality along original generator powers.
This degree-two comparison is needed to identify original global cyclic
classes with the explicit carry cocycles used by the proved local invariant
pairing in DUB-17's principal-product and sum-zero dependency.
-/
namespace Dubon2026
noncomputable section

/-- A two-cocycle on the actual finite cyclic group vanishes when its original generator column vanishes. -/
theorem cyclicTwoCocycle_eq_zero_of_generator_column
    {R G : Type} [CommRing R] [Group G] [Finite G] (A : Rep R G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (c : groupCohomology.cocycles₂ A) (hc : ∀ x, c (x, g) = 0) : c = 0 := by
  have h11 : c (1, 1) = 0 := (groupCohomology.cocycles₂_map_one_fst c g).symm.trans (hc 1)
  have hstep (x y : G) : c (x, y * g) = c (x, y) := by
    have h := (groupCohomology.mem_cocycles₂_iff c).mp c.property x y g
    simpa only [hc, map_zero, zero_add] using h.symm
  apply groupCohomology.cocycles₂_ext
  intro x y
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr (hg y) : y ∈ Submonoid.powers g)
  change c (x, g ^ n) = 0
  induction n with
  | zero => simp only [pow_zero, groupCohomology.cocycles₂_map_one_snd, h11, map_zero]
  | succ n ih => rw [pow_succ, hstep, ih]

/-- Equality of original generator columns is equality of the original finite cyclic two-cocycles. -/
theorem cyclicTwoCocycle_eq_of_generator_column
    {R G : Type} [CommRing R] [Group G] [Finite G] (A : Rep R G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (c d : groupCohomology.cocycles₂ A) (h : ∀ x, c (x, g) = d (x, g)) : c = d := by
  apply sub_eq_zero.mp
  apply cyclicTwoCocycle_eq_zero_of_generator_column A g hg
  intro x
  change c (x, g) - d (x, g) = 0
  exact sub_eq_zero.mpr (h x)

end
end Dubon2026
