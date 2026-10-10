import Dubon2026.ContinuousTraceZeroCocycles

/-! # Genuine continuous trace-zero coboundaries and the original adjoint inclusion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual continuous degree-zero coboundary from the original trace-zero coefficient representation. -/
def continuousTraceZeroAdjointCoboundary (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : matrixTraceZeroSubmodule ι R →ₗ[R] continuousTraceZeroAdjointCocycles ρ where
  toFun X := ⟨⟨groupCohomology.d₀₁ (matrixTraceZeroAdjointRep ρ) X,
    groupCohomology.d₀₁_apply_mem_cocycles₁ (A := matrixTraceZeroAdjointRep ρ) X⟩,
    (matrixAdjointCoboundary_continuous ρ hρ X.val).subtype_mk _⟩
  map_add' X Y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (groupCohomology.d₀₁ (matrixTraceZeroAdjointRep ρ)).hom X Y
  map_smul' r X := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (groupCohomology.d₀₁ (matrixTraceZeroAdjointRep ρ)).hom r X

/-- The range of the genuine original trace-zero coefficient coboundary, without enlarging the allowed coefficient matrices. -/
def continuousTraceZeroAdjointCoboundaries (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : Submodule R (continuousTraceZeroAdjointCocycles ρ) :=
  LinearMap.range (continuousTraceZeroAdjointCoboundary ρ hρ)

omit [IsTopologicalGroup G] in
/-- The actual continuous inclusion preserves the original trace-zero coefficient coboundary as the same full adjoint coboundary. -/
theorem continuousTraceZeroCocycleInclusion_coboundary
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (X : matrixTraceZeroSubmodule ι R) :
    continuousTraceZeroCocycleInclusion ρ (continuousTraceZeroAdjointCoboundary ρ hρ X) =
      continuousMatrixAdjointCoboundary ρ hρ X.val := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

end

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalGroup G] in
/-- When the original matrix dimension is invertible, an actual trace-zero coefficient cocycle is a full adjoint coboundary precisely when it is a coboundary of an actual trace-zero coefficient matrix. -/
theorem continuousTraceZeroCocycleInclusion_mem_coboundaries_iff
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousTraceZeroCocycleInclusion ρ c ∈ continuousMatrixAdjointCoboundaries ρ hρ ↔
      c ∈ continuousTraceZeroAdjointCoboundaries ρ hρ := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨Y, hY, hYX⟩ := matrixAdjointCoboundary_traceFree_representative hn ρ X
    refine ⟨⟨Y, hY⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply Subtype.ext
    exact (hYX g).trans (congrArg (fun z : continuousMatrixAdjointCocycles ρ => z.val g) hX)
  · rintro ⟨X, rfl⟩
    exact ⟨X.val, (continuousTraceZeroCocycleInclusion_coboundary ρ hρ X).symm⟩

end
end Dubon2026
