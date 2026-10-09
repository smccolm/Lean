import Dubon2026.HomogeneousSymmetricBaseChange
import Dubon2026.UniversalMatrixPolynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! # Continuity of the actual symmetric-power general-linear homomorphism -/

namespace Dubon2026

noncomputable section
open MvPolynomial Matrix Module

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Each literal matrix entry of the actual symmetric-power homomorphism is evaluation of its original universal coefficient polynomial. -/
theorem homogeneousSymmetricGL_entry_polynomial (n : ℕ) (i j : Fin (n + 1))
    (g : GeneralLinearGroup (Fin 2) R) :
    (homogeneousSymmetricGL n g).val i j =
      MvPolynomial.eval (fun ij => g.val ij.1 ij.2)
        (matrixCoefficientPolynomial (binaryHomogeneousMonomialBasis n j).val
          (((binaryHomogeneousExponentEquiv n).trans Fin.revPerm).symm i).val) := by
  rw [homogeneousSymmetricGL_val, LinearMap.toMatrix_apply,
    binaryHomogeneousMonomialBasis_repr, matrixCoefficientPolynomial_eval]
  rfl

/-- The actual symmetric-power matrix entries vary continuously over the original topological coefficient ring. -/
theorem homogeneousSymmetricGL_continuous_val (n : ℕ) :
    Continuous (fun g : GeneralLinearGroup (Fin 2) R => (homogeneousSymmetricGL n g).val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [homogeneousSymmetricGL_entry_polynomial]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) R)))

/-- The genuine symmetric-power homomorphism is continuous as a map of general-linear groups, including both the matrix and inverse coordinates. -/
theorem homogeneousSymmetricGL_continuous (n : ℕ) :
    Continuous (homogeneousSymmetricGL (R := R) n) := by
  apply Units.continuous_iff.mpr
  refine ⟨homogeneousSymmetricGL_continuous_val n, ?_⟩
  have hc := (homogeneousSymmetricGL_continuous_val (R := R) n).comp continuous_inv
  simpa only [map_inv] using hc

end
end Dubon2026
