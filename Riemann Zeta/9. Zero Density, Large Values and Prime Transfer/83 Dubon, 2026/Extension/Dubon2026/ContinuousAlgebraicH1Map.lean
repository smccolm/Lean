import Dubon2026.ContinuousRepresentationCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # The literal continuous-to-algebraic H1 map

Retain every original cocycle and its degree-zero coboundary. This is the
degree-one side of the comparison between the continuous connecting map
and the original algebraic relation obstruction used in DUB-17's duality.
-/
namespace Dubon2026
noncomputable section
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Forget continuity while preserving the original H1 cocycle and boundary. -/
def continuousH1ToAlgebraic :
    ContinuousRepresentationH1 A hA →ₗ[R] groupCohomology.H1 A :=
  (continuousRepresentationCoboundariesOne A hA).liftQ
    ((groupCohomology.H1π A).hom.comp (continuousRepresentationCocyclesOne A).subtype)
    (by
      rintro _ ⟨u, rfl⟩
      change groupCohomology.H1π A (continuousRepresentationCoboundaryOne A hA u).val = 0
      apply (groupCohomology.H1π_eq_zero_iff _).mpr
      exact ⟨u, rfl⟩)

omit [IsTopologicalGroup G] in
/-- The actual H1 comparison retains the same original cocycle representative. -/
theorem continuousH1ToAlgebraic_mk (c : continuousRepresentationCocyclesOne A) :
    continuousH1ToAlgebraic A hA (Submodule.Quotient.mk c) =
      groupCohomology.H1π A c.val := rfl

end
end Dubon2026
