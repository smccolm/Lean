import Dubon2026.ContinuousAlgebraicH1Injection
import Dubon2026.ContinuousCocyclePeriodInvariants
import Dubon2026.ContinuousCohomologyRestriction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! DUB-17's local unramified condition: obtain finite inflation stages
from the original continuous inertia kernel. Native compact/discrete
periods are taken after correcting the inertia coboundary, avoiding a
separately assumed coefficient-trivial stage. The quotient dimension and
actual local arithmetic depth remain separate obligations. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- The zero set of an actual one-cocycle is a subgroup, even when the
coefficient action is nontrivial. -/
def cocycleZeroSubgroup (c : groupCohomology.cocycles₁ A) : Subgroup G where
  carrier := {g | c g = 0}
  one_mem' := groupCohomology.cocycles₁_map_one c
  mul_mem' := by
    intro g h hg hh
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property g h
    change c (g * h) = A.ρ g (c h) + c g at hc
    exact hc.trans (by rw [hh, hg, map_zero, add_zero])
  inv_mem' := by
    intro g hg
    change c g = 0 at hg
    have h := (groupCohomology.mem_cocycles₁_iff _).mp c.property g⁻¹ g
    change c (g⁻¹ * g) = A.ρ g⁻¹ (c g) + c g⁻¹ at h
    change c g⁻¹ = 0
    simpa only [inv_mul_cancel, groupCohomology.cocycles₁_map_one, hg, map_zero,
      zero_add] using h.symm

/-- A cocycle vanishing on a normal subgroup represents a class in the
literal first inflation image, by the original exact sequence. -/
theorem cocycle_mem_firstInflation_range (N : Subgroup G) [N.Normal]
    (c : groupCohomology.cocycles₁ A) (hc : ∀ n ∈ N, c n = 0) :
    groupCohomology.H1π A c ∈ (groupCohomology.H1InfRes A N).f.hom.range := by
  rw [(groupCohomology.H1InfRes_exact A N).moduleCat_range_eq_ker]
  change groupCohomology.map N.subtype (𝟙 _) 1 (groupCohomology.H1π A c) = 0
  rw [groupCohomology.H1π_comp_map_apply]
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  refine ⟨0, ?_⟩
  funext n
  change A.ρ n.val 0 - 0 = c n.val
  rw [map_zero, sub_zero, hc n.val n.property]

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Every original continuous class trivial on inertia belongs, after
the injective continuous-to-algebraic comparison, to inflation from the
quotient by inertia and an actual open normal subgroup. -/
theorem continuous_unramified_class_mem_finite_inflation
    (I : Subgroup G) [I.Normal] (x : ContinuousRepresentationH1 A hA)
    (hx : continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val x = 0) :
    ∃ U : OpenNormalSubgroup G,
      continuousH1ToAlgebraic A hA x ∈
        (groupCohomology.H1InfRes A (I ⊔ U.toSubgroup)).f.hom.range := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousRepresentationH1Restriction_mk] at hx
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    let d := c - continuousRepresentationCoboundaryOne A hA m
    have hI : I ≤ cocycleZeroSubgroup A d.val := by
      intro i hi
      have he := congrArg (fun z => z.val.val ⟨i, hi⟩) hm
      change A.ρ i m - m = c.val i at he
      change c.val i - (A.ρ i m - m) = 0
      exact sub_eq_zero.mpr he.symm
    obtain ⟨U, hp, _⟩ := continuousCocycle_exists_openNormal_periods_and_fixed A d
    have hU : U.toSubgroup ≤ cocycleZeroSubgroup A d.val := by
      intro u hu
      have h := hp 1 u hu
      simpa only [one_mul, groupCohomology.cocycles₁_map_one] using h
    have hclass : groupCohomology.H1π A d.val = groupCohomology.H1π A c.val := by
      change groupCohomology.H1π A (c.val -
        (continuousRepresentationCoboundaryOne A hA m).val) = _
      rw [map_sub, sub_eq_self]
      exact (groupCohomology.H1π_eq_zero_iff _).mpr ⟨m, rfl⟩
    refine ⟨U, ?_⟩
    rw [continuousH1ToAlgebraic_mk, ← hclass]
    exact cocycle_mem_firstInflation_range A (I ⊔ U.toSubgroup) d.val
      (fun n hn => (sup_le hI hU) hn)

end
end Dubon2026
