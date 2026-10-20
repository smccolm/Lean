import Dubon2026.PolarizedContinuousFirstOrder
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The full polarized adjoint, rather than the trace-zero fixed-determinant
adjoint, controls the source tangent dimension in DUB-17. The native
continuous differential and pinned rank-nullity theorem give its exact
change-of-basis dimension. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace K] [DiscreteTopology K]
  (ρ : G →* PolarizedGaloisGroup ι K) (hρ : Continuous ρ)

/-- The actual continuous full-adjoint coboundary kernel is exactly the original polarized invariant submodule. -/
theorem continuousPolarizedAdjointCoboundary_ker :
    (continuousRepresentationCoboundaryOne (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ)).ker =
      Representation.invariants (polarizedAdjointRepresentation.comp ρ) := by
  ext X
  rw [LinearMap.mem_ker, Representation.mem_invariants]
  constructor
  · intro h g
    have hg := congrArg (fun c : continuousRepresentationCocyclesOne (polarizedAdjointRep ρ) => c.val g) h
    exact sub_eq_zero.mp hg
  · intro h
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    exact sub_eq_zero.mpr (h g)

/-- The source full-adjoint coboundaries and its invariant matrices account for the whole matrix dimension. -/
theorem continuousPolarizedAdjointCoboundaries_finrank_add_invariants :
    Module.finrank K (continuousRepresentationCoboundariesOne (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ)) +
      Module.finrank K (Representation.invariants (polarizedAdjointRepresentation.comp ρ)) =
        Fintype.card ι ^ 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := Matrix ι ι K)
    (continuousRepresentationCoboundaryOne (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ))
  rw [continuousPolarizedAdjointCoboundary_ker ρ hρ] at h
  simpa only [continuousRepresentationCoboundariesOne, Module.finrank_matrix,
    CommSemiring.finrank_self, mul_one, pow_two] using h

/-- The actual full-adjoint continuous cocycles satisfy the original framed versus strict-class dimension formula. -/
theorem continuousPolarizedAdjointCocycles_finrank_add_invariants
    [Module.Finite K (continuousRepresentationCocyclesOne (polarizedAdjointRep ρ))] :
    Module.finrank K (continuousRepresentationCocyclesOne (polarizedAdjointRep ρ)) +
      Module.finrank K (Representation.invariants (polarizedAdjointRepresentation.comp ρ)) =
    Module.finrank K (ContinuousRepresentationH1 (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ)) + Fintype.card ι ^ 2 := by
  have h := Submodule.finrank_quotient_add_finrank
    (continuousRepresentationCoboundariesOne (polarizedAdjointRep ρ)
      (polarizedAdjointAction_continuous ρ hρ))
  rw [← h, add_assoc, continuousPolarizedAdjointCoboundaries_finrank_add_invariants ρ hρ]

end
end Dubon2026
