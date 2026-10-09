import Dubon2026.DeterminantCharacteristicPolynomial
import Dubon2026.MatrixCharacteristicContinuity
import Dubon2026.SymmetricRepresentationReduction

/-! # Continuity of the actual representation determinant family -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [TopologicalSpace G]
    [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]

/-- A continuous original representation has continuous characteristic coefficients for its actual determinant family. -/
theorem determinantCharacteristicPolynomial_continuous
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) (k : ℕ) :
    Continuous (fun g => (determinantCharacteristicPolynomial ρ g).coeff k) := by
  simp_rw [determinantCharacteristicPolynomial_eq]
  exact (matrixCharacteristicCoefficient_continuous k).comp
    ((Units.continuous_val (M := Matrix ι ι R)).comp hρ)

/-- Every genuine symmetric-power determinant family has continuous characteristic coefficients when the original rank-two representation is continuous. -/
theorem symmetricMatrixRepresentation_determinant_continuous (n : ℕ)
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (hρ : Continuous ρ) (k : ℕ) :
    Continuous (fun g =>
      (determinantCharacteristicPolynomial (symmetricMatrixRepresentation n ρ) g).coeff k) :=
  determinantCharacteristicPolynomial_continuous _
    (symmetricMatrixRepresentation_continuous n ρ hρ) k

end
end Dubon2026
