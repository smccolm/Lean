import Dubon2026.ContinuousRepresentationCohomology

/-! # Exact comparison of original continuous H2 with pinned algebraic H2 for discrete groups -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- Forget continuity by sending the original two-cocycle to the pinned
algebraic H2 class. Every original continuous coboundary has the same algebraic
witness; injectivity is not claimed for arbitrary topological groups. -/
def continuousH2ToAlgebraic :
    ContinuousRepresentationH2 A hA →ₗ[R] groupCohomology.H2 A :=
  (continuousRepresentationCoboundariesTwo A hA).liftQ
    ((groupCohomology.H2π A).hom.comp (continuousRepresentationCocyclesTwo A).subtype)
    (by
      rintro _ ⟨f, rfl⟩
      change groupCohomology.H2π A (continuousRepresentationCoboundaryTwo A hA f).val = 0
      apply (groupCohomology.H2π_eq_zero_iff _).mpr
      exact ⟨(f : G → A), rfl⟩)

/-- The forgetful map preserves the actual original cocycle representative. -/
theorem continuousH2ToAlgebraic_mk (c : continuousRepresentationCocyclesTwo A) :
    continuousH2ToAlgebraic A hA (Submodule.Quotient.mk c) =
      groupCohomology.H2π A c.val := by
  rfl

/-- For the actual discrete group topology, every algebraic cochain witness is
continuous, so the original forgetful map is injective. -/
theorem continuousH2ToAlgebraic_injective [DiscreteTopology G] :
    Function.Injective (continuousH2ToAlgebraic A hA) := by
  intro x y
  induction x using Quotient.inductionOn' with
  | h c =>
    induction y using Quotient.inductionOn' with
    | h d =>
      intro h
      change groupCohomology.H2π A c.val = groupCohomology.H2π A d.val at h
      obtain ⟨f, hf⟩ := (groupCohomology.H2π_eq_iff c.val d.val).mp h
      apply (Submodule.Quotient.eq (continuousRepresentationCoboundariesTwo A hA)).mpr
      refine ⟨(⟨f, continuous_of_discreteTopology⟩ : C(G, A)), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hf

/-- On the original discrete group, every pinned algebraic two-cocycle is
jointly continuous, and hence the original forgetful map is surjective. -/
theorem continuousH2ToAlgebraic_surjective [DiscreteTopology G] :
    Function.Surjective (continuousH2ToAlgebraic A hA) := by
  intro x
  refine groupCohomology.H2_induction_on x ?_
  intro c
  exact ⟨Submodule.Quotient.mk (⟨c, continuous_of_discreteTopology⟩ :
    continuousRepresentationCocyclesTwo A), rfl⟩

/-- The actual continuous H2 of a discrete group is coefficient-linearly
equivalent to the pinned original algebraic H2, through the same cocycles. -/
def continuousDiscreteH2Equiv [DiscreteTopology G] :
    ContinuousRepresentationH2 A hA ≃ₗ[R] groupCohomology.H2 A :=
  LinearEquiv.ofBijective (continuousH2ToAlgebraic A hA)
    ⟨continuousH2ToAlgebraic_injective A hA, continuousH2ToAlgebraic_surjective A hA⟩

/-- The discrete comparison retains the exact pinned quotient map on every
original continuous representative. -/
theorem continuousDiscreteH2Equiv_mk [DiscreteTopology G]
    (c : continuousRepresentationCocyclesTwo A) :
    continuousDiscreteH2Equiv A hA (Submodule.Quotient.mk c) =
      groupCohomology.H2π A c.val := by
  rfl

end
end Dubon2026
