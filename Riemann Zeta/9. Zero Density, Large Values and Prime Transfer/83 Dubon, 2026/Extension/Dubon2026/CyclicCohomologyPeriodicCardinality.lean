import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Two-periodic cardinalities in the original cyclic cohomology

The pinned original periodic resolution identifies each positive odd
group with H1 and each positive even group with H2. These exact
isomorphisms supply the cardinality and finiteness inputs for DUB-17's
bounded connecting-image proof of Herbrand multiplicativity, without
requiring any replacement cohomology model.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G : Type} [CommGroup G] [Fintype G]
  (A : Rep ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg

/-- The original odd cyclic cohomology orders equal the original first cohomology order. -/
theorem cyclic_cohomology_odd_card (n : ℕ) :
    Nat.card (groupCohomology A (2 * n + 1)) = Nat.card (groupCohomology A 1) := by
  exact Nat.card_congr ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg
    (2 * n + 1) ⟨n, rfl⟩ ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide)).symm).toLinearEquiv.toEquiv)

/-- The original positive even cyclic cohomology orders equal the original second cohomology order. -/
theorem cyclic_cohomology_even_card (n : ℕ) :
    Nat.card (groupCohomology A (2 * n + 2)) = Nat.card (groupCohomology A 2) := by
  haveI : NeZero (2 * n + 2) := ⟨by omega⟩
  exact Nat.card_congr ((Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg
    (2 * n + 2) ⟨n + 1, by omega⟩ ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide)).symm).toLinearEquiv.toEquiv)

/-- Finiteness of the actual H1 and H2 implies finiteness of every positive original cyclic cohomology group. -/
theorem cyclic_cohomology_positive_finite [Finite (groupCohomology A 1)]
    [Finite (groupCohomology A 2)] (n : ℕ) : Finite (groupCohomology A (n + 1)) := by
  rcases Nat.even_or_odd (n + 1) with he | ho
  · let e := (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg (n + 1) he ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide)).symm).toLinearEquiv.toEquiv
    exact Finite.of_equiv (groupCohomology A 2) e.symm
  · let e := (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (n + 1) ho ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide)).symm).toLinearEquiv.toEquiv
    exact Finite.of_equiv (groupCohomology A 1) e.symm

end
end Dubon2026
