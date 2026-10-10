import Dubon2026.ContinuousTraceZeroCohomology
import Dubon2026.ContinuousAdjointRestriction

/-! # Restriction of genuine continuous trace-zero adjoint cohomology -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G H ι K : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K] [IsTopologicalRing K]

/-- Restrict the actual continuous trace-zero coefficient cocycle along the original continuous homomorphism. -/
def continuousTraceZeroAdjointRestriction (ρ : G →* GeneralLinearGroup ι K)
    (φ : H →* G) (hφ : Continuous φ) :
    continuousTraceZeroAdjointCocycles ρ →ₗ[K]
      continuousTraceZeroAdjointCocycles (ρ.comp φ) where
  toFun c := ⟨⟨fun h => c.val (φ h), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro h k
    apply Subtype.ext
    change (c.val (φ (h * k))).val =
      (ρ (φ h)).val * (c.val (φ k)).val * (ρ (φ h⁻¹)).val + (c.val (φ h)).val
    rw [φ.map_mul, φ.map_inv]
    exact congrArg Subtype.val
      ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property (φ h) (φ k))⟩,
      c.property.comp hφ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction preserves the genuine coboundary of the same original trace-zero matrix. -/
theorem continuousTraceZeroAdjointRestriction_coboundary
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (φ : H →* G) (hφ : Continuous φ) (X : matrixTraceZeroSubmodule ι K) :
    continuousTraceZeroAdjointRestriction ρ φ hφ
      (continuousTraceZeroAdjointCoboundary ρ hρ X) =
        continuousTraceZeroAdjointCoboundary (ρ.comp φ) (hρ.comp hφ) X := by
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro h
  apply Subtype.ext
  change (ρ (φ h)).val * X.val * (ρ (φ h)⁻¹).val - X.val =
    (ρ (φ h)).val * X.val * (ρ (φ h⁻¹)).val - X.val
  rw [φ.map_inv]

/-- The genuine trace-zero cocycle restriction descends to its actual continuous first cohomology. -/
def continuousTraceZeroH1Restriction (ρ : G →* GeneralLinearGroup ι K)
    (hρ : Continuous ρ) (φ : H →* G) (hφ : Continuous φ) :
    ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[K]
      ContinuousTraceZeroAdjointH1 (ρ.comp φ) (hρ.comp hφ) := by
  have hb : continuousTraceZeroAdjointCoboundaries ρ hρ ≤
      (continuousTraceZeroAdjointCoboundaries (ρ.comp φ) (hρ.comp hφ)).comap
        (continuousTraceZeroAdjointRestriction ρ φ hφ) := by
    rintro _ ⟨X, rfl⟩
    exact ⟨X, (continuousTraceZeroAdjointRestriction_coboundary ρ hρ φ hφ X).symm⟩
  let restrictionMap := Submodule.mapQ (R := K) (R₂ := K)
    (M := continuousTraceZeroAdjointCocycles ρ)
    (M₂ := continuousTraceZeroAdjointCocycles (ρ.comp φ))
    (τ₁₂ := RingHom.id K) (continuousTraceZeroAdjointCoboundaries ρ hρ)
    (continuousTraceZeroAdjointCoboundaries (ρ.comp φ) (hρ.comp hφ))
    (continuousTraceZeroAdjointRestriction ρ φ hφ) hb
  exact restrictionMap

/-- Actual trace-zero cohomology restriction commutes with inclusion into the original full adjoint cohomology. -/
theorem continuousTraceZeroH1Restriction_inclusion
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (φ : H →* G) (hφ : Continuous φ) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousTraceZeroH1Inclusion (ρ.comp φ) (hρ.comp hφ)
      (continuousTraceZeroH1Restriction ρ hρ φ hφ x) =
        continuousMatrixAdjointH1Restriction ρ hρ φ hφ
          (continuousTraceZeroH1Inclusion ρ hρ x) := by
  induction x using Quotient.inductionOn' with
  | h c => rfl

/-- Under the original nonzero-dimension condition, actual trace-zero restriction vanishes exactly when the same included full-adjoint class restricts to zero. -/
theorem continuousTraceZeroH1Restriction_eq_zero_iff
    (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) (hρ : Continuous ρ)
    (φ : H →* G) (hφ : Continuous φ) (x : ContinuousTraceZeroAdjointH1 ρ hρ) :
    continuousTraceZeroH1Restriction ρ hρ φ hφ x = 0 ↔
      continuousMatrixAdjointH1Restriction ρ hρ φ hφ
        (continuousTraceZeroH1Inclusion ρ hρ x) = 0 := by
  rw [← continuousTraceZeroH1Restriction_inclusion]
  constructor
  · intro hx
    rw [hx, map_zero]
  · intro hx
    apply continuousTraceZeroH1ToFixedDeterminant_injective hn (ρ.comp φ) (hρ.comp hφ)
    apply Subtype.ext
    change continuousTraceZeroH1Inclusion (ρ.comp φ) (hρ.comp hφ)
      (continuousTraceZeroH1Restriction ρ hρ φ hφ x) =
        continuousTraceZeroH1Inclusion (ρ.comp φ) (hρ.comp hφ) 0
    rwa [map_zero]

end
end Dubon2026
