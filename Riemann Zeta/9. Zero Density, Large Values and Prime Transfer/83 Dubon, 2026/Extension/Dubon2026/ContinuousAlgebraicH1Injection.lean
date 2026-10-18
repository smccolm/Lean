import Dubon2026.ContinuousAlgebraicH1Map

/-! A degree-one algebraic coboundary already has a degree-zero coefficient
witness. It is therefore continuous for the original continuous action.
This identifies the finite-H1 lifts in DUB-17's local cup-total comparison
with the required restricted continuous class, without an H2 assumption. -/
namespace Dubon2026
noncomputable section
variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

omit [IsTopologicalGroup G] in
/-- Equality of the original algebraic H1 classes reflects equality of
their continuous H1 classes, using the same degree-zero witness. -/
theorem continuousH1ToAlgebraic_injective :
    Function.Injective (continuousH1ToAlgebraic A hA) := by
  intro x y
  induction x using Quotient.inductionOn' with
  | h c =>
    induction y using Quotient.inductionOn' with
    | h d =>
      intro h
      change groupCohomology.H1π A c.val = groupCohomology.H1π A d.val at h
      obtain ⟨u, hu⟩ := (groupCohomology.H1π_eq_iff c.val d.val).mp h
      apply (Submodule.Quotient.eq (continuousRepresentationCoboundariesOne A hA)).mpr
      refine ⟨u, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hu

end
end Dubon2026
