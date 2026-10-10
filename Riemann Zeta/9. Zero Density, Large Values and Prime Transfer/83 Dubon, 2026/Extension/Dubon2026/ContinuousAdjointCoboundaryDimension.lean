import Dubon2026.ContinuousAdjointCohomology
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Actual adjoint invariants and the genuine continuous coboundary dimension -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalRing K]

/-- The kernel of the actual continuous adjoint coboundary map is the original adjoint representation's invariant matrix submodule. -/
theorem continuousMatrixAdjointCoboundary_ker (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) :
    (continuousMatrixAdjointCoboundary ρ hρ).ker = (matrixAdjointRepresentation ρ).invariants := by
  ext X
  rw [LinearMap.mem_ker, Representation.mem_invariants]
  constructor
  · intro h g
    have hg := congrArg (fun c : continuousMatrixAdjointCocycles ρ => c.val g) h
    exact sub_eq_zero.mp hg
  · intro h
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    exact sub_eq_zero.mpr (h g)

/-- Genuine continuous adjoint coboundaries and actual invariant matrices account for the entire original matrix dimension. -/
theorem continuousMatrixAdjointCoboundaries_finrank_add_invariants
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Module.finrank K (continuousMatrixAdjointCoboundaries ρ hρ) +
      Module.finrank K (matrixAdjointRepresentation ρ).invariants = Fintype.card ι ^ 2 := by
  letI : AddCommGroup (groupCohomology.cocycles₁ (matrixAdjointRep ρ)) :=
    (groupCohomology.cocycles₁ (matrixAdjointRep ρ)).addCommGroup
  letI : AddCommGroup (continuousMatrixAdjointCocycles ρ) :=
    (continuousMatrixAdjointCocycles ρ).addCommGroup
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := Matrix ι ι K) (V₂ := continuousMatrixAdjointCocycles ρ)
      (continuousMatrixAdjointCoboundary ρ hρ)
  rw [continuousMatrixAdjointCoboundary_ker] at h
  simpa only [continuousMatrixAdjointCoboundaries, Module.finrank_matrix, CommSemiring.finrank_self,
    mul_one, pow_two] using h

end
end Dubon2026
