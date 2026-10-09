import Dubon2026.ContinuousAdjointCohomology

/-! # Restriction of actual continuous adjoint classes and original lifts -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- Actual restriction along the original continuous group homomorphism preserves the original continuous adjoint cocycle. -/
def continuousMatrixAdjointRestriction (ρ : G →* GeneralLinearGroup ι R)
    (φ : H →* G) (hφ : Continuous φ) :
    continuousMatrixAdjointCocycles ρ →ₗ[R] continuousMatrixAdjointCocycles (ρ.comp φ) where
  toFun c := ⟨⟨fun h => c.val (φ h), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro h k
    change c.val (φ (h * k)) =
      (ρ (φ h)).val * c.val (φ k) * (ρ (φ h⁻¹)).val + c.val (φ h)
    rw [φ.map_mul, φ.map_inv]
    exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.property (φ h) (φ k)⟩,
      c.property.comp hφ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Original restriction commutes with the actual continuous coboundary map. -/
theorem continuousMatrixAdjointRestriction_coboundary (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (φ : H →* G) (hφ : Continuous φ) (X : Matrix ι ι R) :
    continuousMatrixAdjointRestriction ρ φ hφ (continuousMatrixAdjointCoboundary ρ hρ X) =
      continuousMatrixAdjointCoboundary (ρ.comp φ) (hρ.comp hφ) X := by
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro h
  change (ρ (φ h)).val * X * (ρ (φ h)⁻¹).val - X =
    (ρ (φ h)).val * X * (ρ (φ h⁻¹)).val - X
  rw [φ.map_inv]

/-- The original restriction on genuine continuous first cohomology, induced from actual cocycle restriction. -/
def continuousMatrixAdjointH1Restriction (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (φ : H →* G) (hφ : Continuous φ) :
    ContinuousMatrixAdjointH1 ρ hρ →ₗ[R]
      ContinuousMatrixAdjointH1 (ρ.comp φ) (hρ.comp hφ) :=
  by
    have hb : continuousMatrixAdjointCoboundaries ρ hρ ≤
        (continuousMatrixAdjointCoboundaries (ρ.comp φ) (hρ.comp hφ)).comap
          (continuousMatrixAdjointRestriction ρ φ hφ) := by
      rintro _ ⟨X, rfl⟩
      refine ⟨X, ?_⟩
      exact (continuousMatrixAdjointRestriction_coboundary ρ hρ φ hφ X).symm
    let restrictionMap := Submodule.mapQ (R := R) (R₂ := R)
      (M := continuousMatrixAdjointCocycles ρ)
      (M₂ := continuousMatrixAdjointCocycles (ρ.comp φ))
      (τ₁₂ := RingHom.id R) (continuousMatrixAdjointCoboundaries ρ hρ)
      (continuousMatrixAdjointCoboundaries (ρ.comp φ) (hρ.comp hφ))
      (continuousMatrixAdjointRestriction ρ φ hφ) hb
    exact restrictionMap


/-- The actual first-order representation restricts by composition with the original group homomorphism. -/
def matrixFirstOrderLiftRestriction (ρ : G →* GeneralLinearGroup ι R)
    (τ : MatrixFirstOrderLift ρ) (φ : H →* G) : MatrixFirstOrderLift (ρ.comp φ) :=
  ⟨τ.val.comp φ, by
    apply MonoidHom.ext
    intro h
    exact DFunLike.congr_fun τ.property (φ h)⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The original cohomology restriction sends the class of a genuine continuous lift to the class of its actual restricted representation. -/
theorem continuousMatrixAdjointH1Restriction_class (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (φ : H →* G) (hφ : Continuous φ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixAdjointH1Restriction ρ hρ φ hφ
      (continuousMatrixFirstOrderClass ρ hρ τ hτ) =
        continuousMatrixFirstOrderClass (ρ.comp φ) (hρ.comp hφ)
          (matrixFirstOrderLiftRestriction ρ τ φ) (hτ.comp hφ) := rfl

end
end Dubon2026
