import Dubon2026.CoordinateCocycleLinearity
import Dubon2026.SymmetricRepresentationCoordinates
import Dubon2026.SymmetricFirstOrderLifts

/-! # Actual linear pullback of coordinate derivations under genuine symmetric powers -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G R : Type} [Group G] [CommRing R]

/-- The original symmetric-power coordinate map preserves the actual constant dual-number point. -/
theorem symmetricRepresentationCoordinateConstantLift (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    representationCoordinateConstantLift (symmetricMatrixRepresentation n ρ) =
      (representationCoordinateConstantLift ρ).comp (symmetricRepresentationCoordinateMap G R n) := by
  unfold representationCoordinateConstantLift
  rw [symmetricRepresentationCoordinateMap_evaluation, AlgHom.comp_assoc]

/-- The actual symmetric coordinate map induces a genuine linear map on the original point's coordinate derivations. -/
def symmetricCoordinateDerivationMap (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) R) :
    RepresentationCoordinateDerivations ρ →ₗ[R]
      RepresentationCoordinateDerivations (symmetricMatrixRepresentation n ρ) := by
  let A := RepresentationCoordinateAlgebra G (Fin (n + 1)) R
  let B := RepresentationCoordinateAlgebra G (Fin 2) R
  let φ : A →ₐ[R] B := symmetricRepresentationCoordinateMap G R n
  letI := φ.toRingHom.toAlgebra
  letI := (representationCoordinateConstantLift ρ).toRingHom.toAlgebra
  letI := (representationCoordinateConstantLift (symmetricMatrixRepresentation n ρ)).toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algHom φ
  letI : IsScalarTower R B (DualNumber R) := IsScalarTower.of_algHom (representationCoordinateConstantLift ρ)
  letI : IsScalarTower A B (DualNumber R) := IsScalarTower.of_algebraMap_eq (fun x => by
    change representationCoordinateConstantLift (symmetricMatrixRepresentation n ρ) x =
      representationCoordinateConstantLift ρ (φ x)
    exact DFunLike.congr_fun (symmetricRepresentationCoordinateConstantLift n ρ) x)
  let pullback := Derivation.compAlgebraMapL R A B (TrivSqZeroExt.kerIdeal R R)
  exact pullback.restrictScalars R

/-- The actual linear derivative map is literal precomposition with the genuine symmetric-power coordinate map. -/
theorem symmetricCoordinateDerivationMap_apply (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (d : RepresentationCoordinateDerivations ρ)
    (x : RepresentationCoordinateAlgebra G (Fin (n + 1)) R) :
    symmetricCoordinateDerivationMap n ρ d x = d (symmetricRepresentationCoordinateMap G R n x) := rfl

/-- The original square-zero coordinate lift commutes with the actual symmetric-power derivative pullback. -/
theorem symmetricCoordinateDerivationMap_lift (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (d : RepresentationCoordinateDerivations ρ) :
    (representationCoordinateDerivationEquiv (symmetricMatrixRepresentation n ρ)
      (symmetricCoordinateDerivationMap n ρ d)).val =
        (representationCoordinateDerivationEquiv ρ d).val.comp
          (symmetricRepresentationCoordinateMap G R n) := by
  apply AlgHom.ext
  intro x
  rw [representationCoordinateDerivationEquiv_apply, AlgHom.comp_apply,
    representationCoordinateDerivationEquiv_apply, symmetricCoordinateDerivationMap_apply]
  have hc := DFunLike.congr_fun (symmetricRepresentationCoordinateConstantLift n ρ) x
  rw [hc]
  rfl

/-- The genuine linear derivative map produces exactly the original symmetric power of the corresponding original first-order matrix lift. -/
theorem symmetricCoordinateDerivationMap_firstOrder (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (d : RepresentationCoordinateDerivations ρ) :
    firstOrderRepresentationCoordinateEquiv (symmetricMatrixRepresentation n ρ)
      (representationCoordinateDerivationEquiv (symmetricMatrixRepresentation n ρ)
        (symmetricCoordinateDerivationMap n ρ d)) =
      symmetricFirstOrderLift n ρ
        (firstOrderRepresentationCoordinateEquiv ρ (representationCoordinateDerivationEquiv ρ d)) := by
  apply Subtype.ext
  change representationFromCoordinates
    (representationCoordinateDerivationEquiv (symmetricMatrixRepresentation n ρ)
      (symmetricCoordinateDerivationMap n ρ d)).val =
    symmetricMatrixRepresentation n
      (representationFromCoordinates (representationCoordinateDerivationEquiv ρ d).val)
  rw [symmetricCoordinateDerivationMap_lift, representationFromCoordinates_comp]
  have hu : representationFromCoordinates (symmetricRepresentationCoordinateMap G R n) =
      symmetricMatrixRepresentation n (universalMatrixRepresentation G (Fin 2) R) :=
    symmetricRepresentationCoordinateMap_universal G R n
  rw [hu, symmetricMatrixRepresentation_map]
  rfl

end
end Dubon2026
