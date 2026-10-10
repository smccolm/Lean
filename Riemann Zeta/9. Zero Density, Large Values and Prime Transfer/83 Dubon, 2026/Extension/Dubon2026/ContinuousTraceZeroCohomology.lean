import Dubon2026.ContinuousTraceZeroCoboundaries

/-! # Actual continuous H1 of trace-zero coefficients and its original trace-kernel comparison -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [IsTopologicalRing K]

/-- The actual continuous trace-zero cocycle module has its inherited additive group. -/
instance continuousTraceZeroAdjointCocyclesAddCommGroup
    (ρ : G →* GeneralLinearGroup ι K) : AddCommGroup (continuousTraceZeroAdjointCocycles ρ) := by
  letI : AddCommGroup (matrixTraceZeroAdjointRep ρ) :=
    (matrixTraceZeroSubmodule ι K).addCommGroup
  letI : AddCommGroup (groupCohomology.cocycles₁ (matrixTraceZeroAdjointRep ρ)) :=
    (groupCohomology.cocycles₁ (matrixTraceZeroAdjointRep ρ)).addCommGroup
  exact (continuousTraceZeroAdjointCocycles ρ).addCommGroup

/-- The genuine continuous first cohomology of the original trace-zero coefficient representation. -/
abbrev ContinuousTraceZeroAdjointH1 (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :=
  letI := Submodule.hasQuotient (R := K) (M := continuousTraceZeroAdjointCocycles ρ)
  (continuousTraceZeroAdjointCocycles ρ : Type) ⧸ continuousTraceZeroAdjointCoboundaries ρ hρ

/-- The original continuous trace-zero cohomology has its actual quotient additive structure. -/
instance continuousTraceZeroAdjointH1AddCommGroup (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) : AddCommGroup (ContinuousTraceZeroAdjointH1 ρ hρ) := by
  let quotientGroup := Submodule.Quotient.addCommGroup (R := K)
    (M := continuousTraceZeroAdjointCocycles ρ) (continuousTraceZeroAdjointCoboundaries ρ hρ)
  exact quotientGroup

/-- The original continuous trace-zero cohomology has its actual quotient coefficient module structure. -/
instance continuousTraceZeroAdjointH1Module (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) : Module K (ContinuousTraceZeroAdjointH1 ρ hρ) := by
  let quotientModule := Submodule.Quotient.module (R := K)
    (M := continuousTraceZeroAdjointCocycles ρ) (continuousTraceZeroAdjointCoboundaries ρ hρ)
  exact quotientModule

/-- The actual coefficient inclusion descends from trace-zero cohomology to the original full adjoint cohomology. -/
def continuousTraceZeroH1Inclusion (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[K] ContinuousMatrixAdjointH1 ρ hρ := by
  have hb : continuousTraceZeroAdjointCoboundaries ρ hρ ≤
      (continuousMatrixAdjointCoboundaries ρ hρ).comap (continuousTraceZeroCocycleInclusion ρ) := by
    rintro _ ⟨X, rfl⟩
    exact ⟨X.val, (continuousTraceZeroCocycleInclusion_coboundary ρ hρ X).symm⟩
  let inclusionMap := Submodule.mapQ (R := K) (R₂ := K)
    (M := continuousTraceZeroAdjointCocycles ρ) (M₂ := continuousMatrixAdjointCocycles ρ)
    (τ₁₂ := RingHom.id K) (continuousTraceZeroAdjointCoboundaries ρ hρ)
    (continuousMatrixAdjointCoboundaries ρ hρ) (continuousTraceZeroCocycleInclusion ρ) hb
  exact inclusionMap


omit [IsTopologicalGroup G] in
/-- The genuine trace-zero coefficient class has zero original trace after inclusion. -/
theorem continuousTraceZeroH1Inclusion_mem (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousTraceZeroH1Inclusion ρ hρ x ∈ continuousFixedDeterminantClasses ρ hρ := by
  induction x using Quotient.inductionOn' with
  | h c =>
    change (fun g => Matrix.trace (c.val g).val) = 0
    funext g
    exact (c.val g).property

/-- Include actual continuous trace-zero coefficient classes in the genuine full-adjoint trace kernel. -/
def continuousTraceZeroH1ToFixedDeterminant (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) :
    ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[K] continuousFixedDeterminantClasses ρ hρ :=
  (continuousTraceZeroH1Inclusion ρ hρ).codRestrict _ (continuousTraceZeroH1Inclusion_mem ρ hρ)

omit [IsTopologicalGroup G] in
/-- Actual trace-zero coefficient classes inject into the original adjoint trace kernel when the original matrix dimension is nonzero in the coefficient field. -/
theorem continuousTraceZeroH1ToFixedDeterminant_injective
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Function.Injective (continuousTraceZeroH1ToFixedDeterminant ρ hρ) := by
  intro x y
  induction x using Quotient.inductionOn' with
  | h c =>
    induction y using Quotient.inductionOn' with
    | h d =>
      intro h
      apply (Submodule.Quotient.eq (continuousTraceZeroAdjointCoboundaries ρ hρ)).mpr
      apply (continuousTraceZeroCocycleInclusion_mem_coboundaries_iff hn ρ hρ (c - d)).mp
      have h' : (Submodule.Quotient.mk (continuousTraceZeroCocycleInclusion ρ c) :
          ContinuousMatrixAdjointH1 ρ hρ) =
            Submodule.Quotient.mk (continuousTraceZeroCocycleInclusion ρ d) :=
        congrArg Subtype.val h
      rw [map_sub]
      rwa [Submodule.Quotient.eq] at h'

omit [IsTopologicalGroup G] in
/-- Every original continuous adjoint class with zero trace comes from a genuine continuous trace-zero coefficient class. -/
theorem continuousTraceZeroH1ToFixedDeterminant_surjective
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Function.Surjective (continuousTraceZeroH1ToFixedDeterminant ρ hρ) := by
  intro x
  obtain ⟨c, hc⟩ := Quotient.exists_rep x.val
  change (Submodule.Quotient.mk c : ContinuousMatrixAdjointH1 ρ hρ) = x.val at hc
  have ht : continuousMatrixAdjointTrace ρ c = 0 := by
    change continuousMatrixAdjointH1Trace ρ hρ (Submodule.Quotient.mk c) = 0
    rw [hc]
    exact x.property
  let z : (continuousMatrixAdjointTrace ρ).ker := ⟨c, ht⟩
  let c₀ := (continuousTraceZeroCocycleEquiv ρ).symm z
  refine ⟨Submodule.Quotient.mk c₀, ?_⟩
  apply Subtype.ext
  change (Submodule.Quotient.mk (continuousTraceZeroCocycleInclusion ρ c₀) :
    ContinuousMatrixAdjointH1 ρ hρ) = x.val
  rw [← hc]
  apply congrArg Submodule.Quotient.mk
  exact congrArg Subtype.val ((continuousTraceZeroCocycleEquiv ρ).apply_symm_apply z)

/-- Under the genuine invertible-dimension condition, actual continuous H1 of trace-zero coefficients is coefficient-linearly equivalent to the original adjoint trace kernel. -/
def continuousTraceZeroH1FixedDeterminantEquiv
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    ContinuousTraceZeroAdjointH1 ρ hρ ≃ₗ[K] continuousFixedDeterminantClasses ρ hρ :=
  LinearEquiv.ofBijective (continuousTraceZeroH1ToFixedDeterminant ρ hρ)
    ⟨continuousTraceZeroH1ToFixedDeterminant_injective hn ρ hρ,
      continuousTraceZeroH1ToFixedDeterminant_surjective ρ hρ⟩

omit [IsTopologicalGroup G] in
/-- The actual continuous trace-zero coefficient cohomology comparison is bijective under the explicit original dimension condition. -/
theorem continuousTraceZeroH1FixedDeterminantEquiv_bijective
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ) :
    Function.Bijective (continuousTraceZeroH1FixedDeterminantEquiv hn ρ hρ) :=
  (continuousTraceZeroH1FixedDeterminantEquiv hn ρ hρ).bijective

end
end Dubon2026
