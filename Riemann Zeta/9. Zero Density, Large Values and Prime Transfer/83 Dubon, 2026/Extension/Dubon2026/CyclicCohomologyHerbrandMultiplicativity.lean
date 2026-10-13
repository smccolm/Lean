import Dubon2026.BoundedCardinalityRecurrence
import Dubon2026.ExactCohomologyConnectingCardinality
import Dubon2026.CyclicCohomologyPeriodicCardinality

/-! # Herbrand multiplicativity for the original cyclic cohomology

The original long exact sequence gives a recurrence for the orders of
its actual connecting images. Two-periodic cardinalities and boundedness
force unit growth. This proves the required cardinal product identity
without an extra periodicity-naturality development. Finite outer H1/H2
groups also prove finite middle H1/H2 groups. DUB-17 applies this to the
actual S-unit torsion sequence and finite-index lattice sequence.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The original cyclic cohomology orders multiply across an actual short exact sequence; middle finiteness is derived. -/
theorem cyclic_cohomology_herbrand_cardinality
    {G : Type} [CommGroup G] [Fintype G]
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    [Finite (groupCohomology X.X₁ 1)] [Finite (groupCohomology X.X₁ 2)]
    [Finite (groupCohomology X.X₃ 1)] [Finite (groupCohomology X.X₃ 2)] :
    Finite (groupCohomology X.X₂ 1) ∧ Finite (groupCohomology X.X₂ 2) ∧
      Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) *
          Nat.card (groupCohomology X.X₃ 1) =
        Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2) *
          Nat.card (groupCohomology X.X₃ 2) := by
  have hfinite (n : ℕ) [Finite (groupCohomology X.X₁ n)]
      [Finite (groupCohomology X.X₃ n)] : Finite (groupCohomology X.X₂ n) :=
    finite_exact_module_middle
      (A := groupCohomology X.X₁ n) (B := groupCohomology X.X₂ n) (C := groupCohomology X.X₃ n)
      ((groupCohomology.functor ℤ G n).map X.f).hom
      ((groupCohomology.functor ℤ G n).map X.g).hom
      (groupCohomology.mapShortComplex₂_exact hX n).moduleCat_range_eq_ker
  refine ⟨hfinite 1, hfinite 2, ?_⟩
  let c (n : ℕ) := Nat.card (groupCohomology.δ hX n (n + 1) rfl).hom.range
  let d (n : ℕ) := c (2 * n + 2)
  have hfC (n : ℕ) : Finite (groupCohomology X.X₃ (2 * n + 2)) := by
    simpa only [Nat.add_assoc] using cyclic_cohomology_positive_finite X.X₃ g hg (2 * n + 1)
  have hdpos (n : ℕ) : 0 < d n := by
    letI := hfC n
    let f := (groupCohomology.δ hX (2 * n + 2) (2 * n + 2 + 1) rfl).hom
    letI : Finite f.range := Finite.of_surjective f.rangeRestrict f.surjective_rangeRestrict
    exact Nat.card_pos
  have hdbound (n : ℕ) : d n ≤ Nat.card (groupCohomology X.X₃ 2) := by
    letI := hfC n
    let f := (groupCohomology.δ hX (2 * n + 2) (2 * n + 2 + 1) rfl).hom
    have h := Nat.card_le_card_of_surjective f.rangeRestrict f.surjective_rangeRestrict
    rw [cyclic_cohomology_even_card X.X₃ g hg n] at h
    exact h
  have hodd (A : Rep ℤ G) (n : ℕ) :
      Nat.card (groupCohomology A (2 * n + 3)) = Nat.card (groupCohomology A 1) := by
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega]
    exact cyclic_cohomology_odd_card A g hg (n + 1)
  have heven (A : Rep ℤ G) (n : ℕ) :
      Nat.card (groupCohomology A (2 * n + 4)) = Nat.card (groupCohomology A 2) := by
    rw [show 2 * n + 4 = 2 * (n + 1) + 2 by omega]
    exact cyclic_cohomology_even_card A g hg (n + 1)
  have hrec (n : ℕ) :
      d (n + 1) * (Nat.card (groupCohomology X.X₁ 1) *
          Nat.card (groupCohomology X.X₃ 1) * Nat.card (groupCohomology X.X₂ 2)) =
        d n * (Nat.card (groupCohomology X.X₁ 2) *
          Nat.card (groupCohomology X.X₃ 2) * Nat.card (groupCohomology X.X₂ 1)) := by
    have ho := exact_cohomology_connecting_cardinality X hX (2 * n + 2)
    change Nat.card (groupCohomology X.X₂ (2 * n + 3)) * d n * c (2 * n + 3) =
      Nat.card (groupCohomology X.X₁ (2 * n + 3)) *
        Nat.card (groupCohomology X.X₃ (2 * n + 3)) at ho
    rw [hodd, hodd, hodd] at ho
    have he := exact_cohomology_connecting_cardinality X hX (2 * n + 3)
    change Nat.card (groupCohomology X.X₂ (2 * n + 4)) * c (2 * n + 3) * c (2 * n + 4) =
      Nat.card (groupCohomology X.X₁ (2 * n + 4)) *
        Nat.card (groupCohomology X.X₃ (2 * n + 4)) at he
    rw [heven, heven, heven, show 2 * n + 4 = 2 * (n + 1) + 2 by omega] at he
    change Nat.card (groupCohomology X.X₂ 2) * c (2 * n + 3) * d (n + 1) = _ at he
    rw [← ho, ← he]
    ac_rfl
  have h := bounded_positive_cardinality_recurrence d _ _ _ hdpos hdbound hrec
  calc
    Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) *
        Nat.card (groupCohomology X.X₃ 1) =
      Nat.card (groupCohomology X.X₁ 1) * Nat.card (groupCohomology X.X₃ 1) *
        Nat.card (groupCohomology X.X₂ 2) := by ac_rfl
    _ = Nat.card (groupCohomology X.X₁ 2) * Nat.card (groupCohomology X.X₃ 2) *
        Nat.card (groupCohomology X.X₂ 1) := h
    _ = _ := by ac_rfl

end
end Dubon2026
