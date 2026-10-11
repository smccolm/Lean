import Dubon2026.CyclicTwoCocyclePeriodSum
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Fin

/-! # The literal generator-period sum is the original representation norm -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg

/-- Enumeration by the original generator identifies its actual period
action sum with the original full representation norm. -/
theorem representationCyclicGenerator_sum_eq_norm (a : A) :
    (∑ i ∈ Finset.range (orderOf g), A.ρ (g ^ i) a) = A.ρ.norm a := by
  let e : Subgroup.zpowers g ≃ G := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, hg x⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let E := (finEquivZPowers (isOfFinOrder_of_finite g)).trans e
  have h := E.sum_comp (fun x => A.ρ x a)
  change (∑ i : Fin (orderOf g), A.ρ (g ^ (i : ℕ)) a) = ∑ x : G, A.ρ x a at h
  rw [Finset.sum_range]
  simpa only [Representation.norm, LinearMap.sum_apply] using h

/-- An original coboundary has cyclic period sum exactly equal to the
original representation norm of its genuine generator value. -/
theorem representationCyclicPeriodSum_coboundary_eq_norm (b : G → A) :
    representationCyclicTwoCochainPeriodSum A g (orderOf g) (groupCohomology.d₁₂ A b) =
      A.ρ.norm (b g) := by
  rw [representationCyclicTwoCochainPeriodSum_coboundary A g (orderOf g)
    (pow_orderOf_eq_one g), representationCyclicGenerator_sum_eq_norm A g hg]

end
end Dubon2026
