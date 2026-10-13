import Dubon2026.StableSubmoduleCohomologySequence
import Dubon2026.FiniteCyclicCohomologyCardinality

/-! # Herbrand comparison through the actual finite-index quotient

The actual stable-submodule quotient is finite, hence its original H1
and H2 are finite and have equal positive order. Original cohomological
multiplicativity cancels this order and derives ambient finiteness.
This is the finite-index step required for the constructed permutation
sublattice in DUB-17's S-unit Herbrand calculation.
-/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2
variable {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G)
  (W : Submodule ℤ A) (hW : ∀ g, W ≤ W.comap (A.ρ g))

/-- A genuine finite-index stable submodule has the same original Herbrand cardinal ratio as its ambient representation, whose cohomology finiteness is derived. -/
theorem finiteIndex_herbrand_comparison
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (A ⧸ W)]
    [Finite (groupCohomology (A.subrepresentation W hW) 1)]
    [Finite (groupCohomology (A.subrepresentation W hW) 2)] :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 2) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 1) =
        Nat.card (groupCohomology A 1) *
          Nat.card (groupCohomology (A.subrepresentation W hW) 2) := by
  let X := stableSubmoduleShortComplex A W hW
  letI : Finite X.X₃ := inferInstanceAs (Finite (A ⧸ W))
  letI : Finite (groupCohomology X.X₁ 1) :=
    inferInstanceAs (Finite (groupCohomology (A.subrepresentation W hW) 1))
  letI : Finite (groupCohomology X.X₁ 2) :=
    inferInstanceAs (Finite (groupCohomology (A.subrepresentation W hW) 2))
  letI : Finite (groupCohomology X.X₃ 1) := finite_groupCohomology_of_finite_coefficients X.X₃ 1
  letI : Finite (groupCohomology X.X₃ 2) := finite_groupCohomology_of_finite_coefficients X.X₃ 2
  have h := cyclic_cohomology_herbrand_cardinality X
    (stableSubmoduleShortComplex_shortExact A W hW) g hg
  refine ⟨h.1, h.2.1, ?_⟩
  change Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) =
    Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2)
  have heq := finite_cyclic_first_second_cohomology_card_eq X.X₃ g hg
  have hc := h.2.2
  rw [← heq] at hc
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := groupCohomology X.X₃ 1)) hc

end
end Dubon2026
