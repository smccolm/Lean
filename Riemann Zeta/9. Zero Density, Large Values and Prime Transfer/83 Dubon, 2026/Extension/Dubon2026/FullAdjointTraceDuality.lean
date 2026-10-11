import Dubon2026.FullMatrixTracePairing
import Dubon2026.TraceZeroAdjointRepresentation
import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariance of the genuine full-matrix trace duality -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Conjugation on actual matrices is contragredient to itself under the genuine
trace pairing. The group inverse in the dual representation is retained. -/
theorem fullMatrixTracePairing_adjoint
    (ρ : G →* GeneralLinearGroup ι R) (g : G) (X : Matrix ι ι R) :
    fullMatrixTracePairing (matrixAdjointRepresentation ρ g X) =
      (matrixAdjointRepresentation ρ).dual g (fullMatrixTracePairing X) := by
  ext Y
  change Matrix.trace ((ρ g).val * X * (ρ g⁻¹).val * Y) =
    Matrix.trace (X * ((ρ g⁻¹).val * Y * (ρ (g⁻¹)⁻¹).val))
  simp only [inv_inv]
  calc
    Matrix.trace ((ρ g).val * X * (ρ g⁻¹).val * Y) =
        Matrix.trace ((ρ g).val * (X * ((ρ g⁻¹).val * Y))) := by
          simp only [mul_assoc]
    _ = Matrix.trace ((X * ((ρ g⁻¹).val * Y)) * (ρ g).val) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * ((ρ g⁻¹).val * Y * (ρ g).val)) := by
      simp only [mul_assoc]

/-- The existing perfect full-matrix trace pairing is an equivalence of the
original adjoint representation and its actual linear dual. -/
def fullMatrixAdjointTraceDuality (ρ : G →* GeneralLinearGroup ι R) :
    Representation.Equiv (matrixAdjointRepresentation ρ)
      (matrixAdjointRepresentation ρ).dual where
  toLinearEquiv := fullMatrixTraceDuality
  isIntertwining' g := by
    apply LinearMap.ext
    intro X
    exact fullMatrixTracePairing_adjoint ρ g X

end
end Dubon2026
