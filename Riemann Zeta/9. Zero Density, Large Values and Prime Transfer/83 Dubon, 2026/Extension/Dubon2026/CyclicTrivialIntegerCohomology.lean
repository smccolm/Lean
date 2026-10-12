import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # The original cyclic norm and odd cohomology on integer coefficients -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped BigOperators

/-- The actual norm on the trivial integer representation is multiplication
by the actual finite group cardinality. -/
theorem trivialIntegerRep_norm_apply
    (G : Type) [Group G] [Fintype G] (x : ℤ) :
    (Rep.trivial ℤ G ℤ).norm.hom x = (Fintype.card G : ℤ) * x := by
  change (∑ _ : G, (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) x = _
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card G • x = _
  exact nsmul_eq_mul _ _

/-- The original integer norm has zero kernel. Surjectivity of the actual
odd cyclic cohomology projection therefore makes every odd group zero. -/
theorem cyclic_trivial_integer_odd_cohomology_zero
    (G : Type) [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : Odd n) :
    Limits.IsZero (groupCohomology (Rep.trivial ℤ G ℤ) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (Rep.trivial ℤ G ℤ) g hg n hn
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance x
  have hy : y = 0 := by
    apply Subtype.ext
    have h := y.property
    change (Rep.trivial ℤ G ℤ).norm.hom y.val = 0 at h
    rw [trivialIntegerRep_norm_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hy, map_zero]

end
end Dubon2026
