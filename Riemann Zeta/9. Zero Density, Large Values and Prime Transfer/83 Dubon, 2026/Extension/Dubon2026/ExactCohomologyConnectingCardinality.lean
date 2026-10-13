import Dubon2026.ExactCohomologyCardinality

/-! # Orders of original connecting images in the long exact sequence

Counting actual kernels and images in three consecutive original
cohomology terms gives the multiplicative recurrence used for DUB-17's
Herbrand comparison. No adjacent vanishing or periodic-map naturality
is assumed; the original long exact sequence supplies every exactness
statement.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Three actual exact middle terms give the cardinal identity with both actual boundary images. -/
theorem exact_three_middle_cardinality
    {R P A B C Q : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup Q] [Module R Q]
    (u : P →ₗ[R] A) (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] Q)
    (huf : u.range = f.ker) (hfg : f.range = g.ker) (hgh : g.range = h.ker) :
    Nat.card B * Nat.card u.range * Nat.card h.range = Nat.card A * Nat.card C := by
  rw [linearMap_card_eq_kernel_mul_range f, linearMap_card_eq_kernel_mul_range g,
    linearMap_card_eq_kernel_mul_range h, ← huf, ← hfg, ← hgh]
  ac_rfl

/-- The original cohomology long exact sequence gives the actual connecting-image cardinal recurrence. -/
theorem exact_cohomology_connecting_cardinality
    {R G : Type} [CommRing R] [Group G]
    (X : ShortComplex (Rep R G)) (hX : X.ShortExact) (n : ℕ) :
    Nat.card (groupCohomology X.X₂ (n + 1)) *
        Nat.card (groupCohomology.δ hX n (n + 1) rfl).hom.range *
        Nat.card (groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl).hom.range =
      Nat.card (groupCohomology X.X₁ (n + 1)) * Nat.card (groupCohomology X.X₃ (n + 1)) := by
  exact exact_three_middle_cardinality
    (groupCohomology.δ hX n (n + 1) rfl).hom
    ((groupCohomology.functor R G (n + 1)).map X.f).hom
    ((groupCohomology.functor R G (n + 1)).map X.g).hom
    (groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl).hom
    (groupCohomology.mapShortComplex₁_exact hX rfl).moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₂_exact hX (n + 1)).moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₃_exact hX rfl).moduleCat_range_eq_ker

end
end Dubon2026
