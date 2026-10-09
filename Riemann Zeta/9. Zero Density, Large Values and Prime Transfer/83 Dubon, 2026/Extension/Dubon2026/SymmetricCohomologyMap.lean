import Dubon2026.SymmetricCohomologyKernel
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The genuine linear symmetric-power map on original adjoint first cohomology -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R : Type} [Group G] [CommRing R]

/-- The original symmetric tangent map descends through the actual original adjoint H1 quotient by its proved kernel inclusion. -/
def symmetricAdjointCohomologyMap (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    groupCohomology.H1 (matrixAdjointRep ρ) →ₗ[R]
      groupCohomology.H1 (matrixAdjointRep (symmetricMatrixRepresentation n ρ)) := by
  let q := coordinateTangentCohomologyMap ρ
  let g := symmetricTangentCohomologyLift n ρ
  let descended := Submodule.liftQ (R := R) (R₂ := R)
    (M := RepresentationCoordinateDerivations ρ)
    (M₂ := groupCohomology.H1 (matrixAdjointRep (symmetricMatrixRepresentation n ρ)))
    (τ₁₂ := RingHom.id R) (LinearMap.ker q) g (symmetricTangentCohomologyLift_ker n ρ)
  let quotientEquiv := LinearMap.quotKerEquivOfSurjective (R := R)
    (M := RepresentationCoordinateDerivations ρ)
    (M₂ := groupCohomology.H1 (matrixAdjointRep ρ)) q
    (coordinateTangentCohomologyMap_surjective ρ)
  exact descended.comp quotientEquiv.symm.toLinearMap

/-- The genuine linear symmetric H1 map sends the original tangent class to the class of its actual symmetric derivative. -/
theorem symmetricAdjointCohomologyMap_class (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (d : RepresentationCoordinateDerivations ρ) :
    symmetricAdjointCohomologyMap n ρ (coordinateTangentCohomologyMap ρ d) =
      coordinateTangentCohomologyMap (symmetricMatrixRepresentation n ρ)
        (symmetricCoordinateDerivationMap n ρ d) := by
  unfold symmetricAdjointCohomologyMap
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply,
    symmetricTangentCohomologyLift]

/-- On every original genuine first-order representation, the actual linear cohomology map is precisely the class of its original symmetric-power lift. -/
theorem symmetricAdjointCohomologyMap_firstOrder (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (τ : MatrixFirstOrderLift ρ) :
    symmetricAdjointCohomologyMap n ρ
      (groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ)) =
      groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
        (matrixFirstOrderCocycle _ (symmetricFirstOrderLift n ρ τ)) := by
  let f := (firstOrderRepresentationCoordinateEquiv ρ).symm τ
  let d := (representationCoordinateDerivationEquiv ρ).symm f
  have hd : representationCoordinateDerivationEquiv ρ d = f :=
    (representationCoordinateDerivationEquiv ρ).apply_symm_apply f
  have ht : firstOrderRepresentationCoordinateEquiv ρ
      (representationCoordinateDerivationEquiv ρ d) = τ := by
    rw [hd]
    exact (firstOrderRepresentationCoordinateEquiv ρ).apply_symm_apply τ
  have h := symmetricAdjointCohomologyMap_class n ρ d
  change symmetricAdjointCohomologyMap n ρ
    (groupCohomology.H1π (matrixAdjointRep ρ)
      (matrixFirstOrderCocycle ρ (firstOrderRepresentationCoordinateEquiv ρ
        (representationCoordinateDerivationEquiv ρ d)))) =
    groupCohomology.H1π (matrixAdjointRep (symmetricMatrixRepresentation n ρ))
      (matrixFirstOrderCocycle _ (firstOrderRepresentationCoordinateEquiv _
        (representationCoordinateDerivationEquiv _ (symmetricCoordinateDerivationMap n ρ d)))) at h
  rw [ht, symmetricCoordinateDerivationMap_firstOrder, ht] at h
  exact h

end
end Dubon2026
