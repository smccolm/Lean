import Dubon2026.RepresentationCoordinateEquivalence
import Dubon2026.SymmetricRepresentationReduction

/-! # The actual symmetric-power map on original representation coordinate algebras -/

namespace Dubon2026

noncomputable section
open Matrix

variable (G R : Type*) [Group G] [CommRing R]

/-- The original symmetric power of the genuine universal rank-two representation defines the actual map of coordinate algebras. -/
def symmetricRepresentationCoordinateMap (n : ℕ) :
    RepresentationCoordinateAlgebra G (Fin (n + 1)) R →ₐ[R]
      RepresentationCoordinateAlgebra G (Fin 2) R :=
  representationCoordinateEvaluation (R := R)
    (symmetricMatrixRepresentation n (universalMatrixRepresentation G (Fin 2) R))

/-- Base change of the original universal representation by the coordinate map is exactly the original symmetric power of the universal rank-two representation. -/
theorem symmetricRepresentationCoordinateMap_universal (n : ℕ) :
    (GeneralLinearGroup.map (symmetricRepresentationCoordinateMap G R n).toRingHom).comp
      (universalMatrixRepresentation G (Fin (n + 1)) R) =
        symmetricMatrixRepresentation n (universalMatrixRepresentation G (Fin 2) R) :=
  universalMatrixRepresentation_evaluation _

variable {G R} {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluating the actual symmetric-power coordinate map at an original representation gives the actual coordinate evaluation of that original symmetric-power representation. -/
theorem symmetricRepresentationCoordinateMap_evaluation (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) S) :
    representationCoordinateEvaluation (R := R) (symmetricMatrixRepresentation n ρ) =
      (representationCoordinateEvaluation (R := R) ρ).comp
        (symmetricRepresentationCoordinateMap G R n) := by
  have h := representationCoordinateEvaluation_natural (R := R)
    (symmetricMatrixRepresentation n (universalMatrixRepresentation G (Fin 2) R))
    (representationCoordinateEvaluation (R := R) ρ)
  rw [symmetricMatrixRepresentation_map, universalMatrixRepresentation_evaluation] at h
  exact h

end
end Dubon2026
