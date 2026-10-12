import Dubon2026.CosetTraceOneCocycles

/-! # The original degree-one restriction/corestriction index homotopy

The explicit zero-cochain is the sum of the original cocycle at the actual coset
representatives. This is needed to detect classes after coprime cyclotomic descent.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

/-- A literal trace term of the restricted original one-cocycle differs from
its original value by the exact change of coset-representative values. -/
theorem cosetTraceOneTerm_restriction
    (c : groupCohomology.cocycles₁ A) (g : G) (q : G ⧸ S) :
    cosetTraceOneTerm A S (fun h => c h) g q =
      A.ρ g (c q.out) + c g - c (g • q).out := by
  have h₁ := (groupCohomology.mem_cocycles₁_iff _).mp c.property g q.out
  have h₂ := (groupCohomology.mem_cocycles₁_iff _).mp c.property
    (g • q).out (cosetTransition S g q)
  rw [cosetTransition_factor] at h₂
  exact eq_sub_of_add_eq (h₂.symm.trans h₁)

/-- Tracing the actual restricted cocycle is its index multiple plus the
original coboundary of the explicit sum of representative values. -/
theorem cosetTraceOne_restriction [Fintype (G ⧸ S)] (c : groupCohomology.cocycles₁ A) :
    cosetTraceOne A S (fun h => c h) =
      Fintype.card (G ⧸ S) • (c : G → A) +
        groupCohomology.d₀₁ A (∑ q : G ⧸ S, c q.out) := by
  funext g
  change (∑ q : G ⧸ S, cosetTraceOneTerm A S (fun h => c h) g q) =
    Fintype.card (G ⧸ S) • c g +
      (A.ρ g (∑ q : G ⧸ S, c q.out) - ∑ q : G ⧸ S, c q.out)
  simp only [cosetTraceOneTerm_restriction, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum]
  have hr : (∑ q : G ⧸ S, c (g • q).out) = ∑ q : G ⧸ S, c q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ S => c q.out)
  rw [hr]
  abel

end
end Dubon2026
