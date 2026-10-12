import Dubon2026.CosetTraceDifferential

/-! # The existing original coset trace on degree-one cocycles

This is the degree-one corestriction input for descent of the proved local
Kummer perfect pairing from a cyclotomic extension. The existing trace and
differential are reused with their original coset representatives.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  (S : Subgroup G) [Fintype (G ⧸ S)]

/-- The existing original degree-one coset trace takes actual subgroup
one-cocycles to actual original group one-cocycles. -/
theorem cosetTraceOne_mem_cocycles
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    cosetTraceOne A S c ∈ groupCohomology.cocycles₁ A := by
  change groupCohomology.d₁₂ A (cosetTraceOne A S c) = 0
  rw [← cosetTraceTwo_differential]
  have hc : groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) c = 0 := c.property
  rw [hc, map_zero]

/-- The actual degree-zero trace is the sum of the original coefficient
actions of the same original coset representatives. -/
def cosetTraceZero : A →ₗ[R] A :=
  ∑ q : G ⧸ S, A.ρ q.out

/-- Original degree-one coboundaries trace to original coboundaries of the
literal degree-zero trace, so no degree-one quotient relation is assumed. -/
theorem cosetTraceOne_coboundary (a : A) :
    cosetTraceOne A S (groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype) a) =
      groupCohomology.d₀₁ A (cosetTraceZero A S a) := by
  funext g
  change (∑ q : G ⧸ S, A.ρ (g • q).out
      (A.ρ (cosetTransition S g q) a - a)) =
    A.ρ g ((∑ q : G ⧸ S, A.ρ q.out) a) - (∑ q : G ⧸ S, A.ρ q.out) a
  simp only [map_sub, cosetTransition_action, Finset.sum_sub_distrib, LinearMap.sum_apply]
  rw [← map_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ S => A.ρ q.out a)

end
end Dubon2026
