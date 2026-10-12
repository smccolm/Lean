import Dubon2026.ContinuousCocyclePeriodInvariants
import Dubon2026.ContinuousTwoCocyclePeriodInvariants
import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual low-degree classes vanish on an original open normal subgroup

The existing compact/discrete period theorems supply the subgroup. Explicit
original coboundaries kill its H1 and H2 restrictions, including unnormalized
two-cocycles. This is the finite-coefficient effacement input for DUB-17's
induced-module exact-sequence local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Every actual continuous H1 class restricts to zero on a genuine open
normal subgroup, using the existing original cocycle period theorem. -/
theorem continuousH1_exists_openNormal_restriction_zero (x : ContinuousRepresentationH1 A hA) :
    ∃ U : OpenNormalSubgroup G,
      continuousRepresentationH1Restriction A hA U.toSubgroup.subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨U, hp, _⟩ := continuousCocycle_exists_openNormal_periods_and_fixed A c
    refine ⟨U, ?_⟩
    rw [continuousRepresentationH1Restriction_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext u
    have hu := hp 1 u u.property
    have hz : c.val (u : G) = 0 := by
      simpa only [one_mul, groupCohomology.cocycles₁_map_one] using hu
    change A.ρ (u : G) 0 - 0 = c.val (u : G)
    rw [map_zero, sub_zero, hz]

/-- Every actual continuous H2 class restricts to zero on a genuine open
normal subgroup. A continuous one-cochain with that same constant value
removes the original value, so normalization is unnecessary. -/
theorem continuousH2_exists_openNormal_restriction_zero (x : ContinuousRepresentationH2 A hA) :
    ∃ U : OpenNormalSubgroup G,
      continuousRepresentationH2Restriction A hA U.toSubgroup.subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨U, hp, hfixed⟩ := continuousTwoCocycle_exists_openNormal_periods_and_fixed A c
    refine ⟨U, ?_⟩
    rw [continuousRepresentationH2Restriction_mk]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨ContinuousMap.const U.toSubgroup (c.val (1, 1)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    have hz := hp 1 1 z.1 z.2 z.1.property z.2.property
    change A.ρ (z.1 : G) (c.val (1, 1)) - c.val (1, 1) + c.val (1, 1) =
      c.val (z.1, z.2)
    rw [hfixed z.1 z.1.property, sub_self, zero_add]
    simpa only [one_mul] using hz.symm

end
end Dubon2026
