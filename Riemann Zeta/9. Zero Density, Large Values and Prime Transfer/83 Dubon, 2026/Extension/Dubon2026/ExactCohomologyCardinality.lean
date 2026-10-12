import Dubon2026.FiniteExactModuleCardinality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Cardinalities from the actual cohomology long exact sequence -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- A genuine coefficient short exact sequence, with the adjacent groups
zero, gives the literal four-term cohomology cardinal identity. Finiteness of
the middle group is derived from the actual maps and the finite outer groups. -/
theorem exact_cohomology_four_term_cardinality
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep k G)) (hX : X.ShortExact) (n : ℕ)
    (hprev : Limits.IsZero (groupCohomology X.X₃ n))
    (hnext : Limits.IsZero (groupCohomology X.X₂ (n + 1 + 1)))
    [Finite (groupCohomology X.X₁ (n + 1))]
    [Finite (groupCohomology X.X₃ (n + 1))] :
    Finite (groupCohomology X.X₂ (n + 1)) ∧
      Nat.card (groupCohomology X.X₂ (n + 1)) *
          Nat.card (groupCohomology X.X₁ (n + 1 + 1)) =
        Nat.card (groupCohomology X.X₁ (n + 1)) *
          Nat.card (groupCohomology X.X₃ (n + 1)) := by
  let f := (groupCohomology.functor k G (n + 1)).map X.f
  let g := (groupCohomology.functor k G (n + 1)).map X.g
  let h := groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl
  have hfg : f.hom.range = g.hom.ker :=
    (groupCohomology.mapShortComplex₂_exact hX (n + 1)).moduleCat_range_eq_ker
  have hgh : g.hom.range = h.hom.ker :=
    (groupCohomology.mapShortComplex₃_exact hX (i := n + 1) rfl).moduleCat_range_eq_ker
  have hf : Mono f :=
    (groupCohomology.mapShortComplex₁_exact hX (i := n) rfl).mono_g
      (hprev.eq_of_src _ _)
  have hh : Epi h := groupCohomology.epi_δ_of_isZero hX (n + 1) hnext
  exact ⟨finite_exact_module_middle
      (A := groupCohomology X.X₁ (n + 1))
      (B := groupCohomology X.X₂ (n + 1))
      (C := groupCohomology X.X₃ (n + 1)) f.hom g.hom hfg,
    exact_four_module_cardinality f.hom g.hom h.hom
      ((ModuleCat.mono_iff_injective f).mp hf)
      ((ModuleCat.epi_iff_surjective h).mp hh) hfg hgh⟩

end
end Dubon2026
