import Dubon2026.FiniteProductCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Detection of original product H2 by its actual coordinate maps

Coordinate coboundaries assemble into an original product coboundary.
This supplies the noncyclic outside-support step in local detection of
global unit H2, serving DUB-17 through arithmetic invariant sum-zero and
global duality. No higher-degree product preservation is required.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G ι : Type} [CommRing R] [Group G] (A : ι → Rep R G)

/-- The actual coordinate projection of the original product representation. -/
def originalPiRepProjection (i : ι) : originalPiRep A ⟶ A i :=
  Rep.ofHom ⟨LinearMap.proj i, by intro g; rfl⟩

/-- An original product H2 class is zero if each actual coordinate image is zero. -/
theorem originalPiH2_zero_of_coordinates (x : groupCohomology (originalPiRep A) 2)
    (hx : ∀ i, (groupCohomology.functor R G 2).map (originalPiRepProjection A i) x = 0) :
    x = 0 := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    apply (groupCohomology.H2π_eq_zero_iff c).mpr
    have hc (i : ι) : ∃ b : G → A i,
        groupCohomology.d₁₂ (A i) b = fun g => c g i := by
      let ci := groupCohomology.mapCocycles₂ (MonoidHom.id G) (originalPiRepProjection A i) c
      have hi : groupCohomology.H2π (A i) ci = 0 := by
        have hi := hx i
        change groupCohomology.map (MonoidHom.id G) (originalPiRepProjection A i) 2
          (groupCohomology.H2π (originalPiRep A) c) = 0 at hi
        rwa [groupCohomology.H2π_comp_map_apply] at hi
      exact (groupCohomology.H2π_eq_zero_iff ci).mp hi
    choose b hb using hc
    refine ⟨fun g i => b i g, ?_⟩
    funext g i
    exact congrFun (hb i) g

/-- Vanishing of all original factor H2 groups implies vanishing of their arbitrary product H2. -/
theorem originalPi_second_cohomology_zero
    (hz : ∀ i, Limits.IsZero (groupCohomology (A i) 2)) :
    Limits.IsZero (groupCohomology (originalPiRep A) 2) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  apply originalPiH2_zero_of_coordinates A x
  intro i
  exact (ModuleCat.isZero_iff_subsingleton.mp (hz i)).elim _ _

end
end Dubon2026
