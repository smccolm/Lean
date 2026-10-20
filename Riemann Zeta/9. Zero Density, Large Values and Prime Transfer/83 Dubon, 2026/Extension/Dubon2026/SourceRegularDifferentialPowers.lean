import Dubon2026.SourceRegularDifferentialLie
import Dubon2026.SourceDerivationLocalNilpotence

/-! Nilpotent original matrices act locally nilpotently on the original
polynomial numerators. The determinant denominator will be handled separately
before applying Engel's theorem to the actual source coefficient module.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions R n

/-- Every iterated original differential on a matrix coordinate is the corresponding entry of the generic matrix multiplied by the same power of the original infinitesimal matrix. -/
theorem sourceRegularDifferential_pow_X (X : Matrix (Fin n) (Fin n) R)
    (k : ℕ) (i j : Fin n) :
    ((sourceRegularDifferential X).toLinearMap ^ k)
      (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
      ((generalLinearRegularGeneric R n).val *
        (algebraMap R S).mapMatrix (X ^ k)) i j := by
  induction k with
  | zero => simp [generalLinearRegularGeneric_apply]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change sourceRegularDifferential X
      (((generalLinearRegularGeneric R n).val * (X ^ k).map (algebraMap R S)) i j) = _
    rw [sourceRegularDifferential_generic_mul]
    rw [pow_succ', map_mul, Matrix.mul_assoc]
    rfl

/-- Nilpotence of an actual original matrix yields local nilpotence of its exact differential on every original polynomial numerator. -/
theorem sourceRegularDifferential_polynomial_locallyNilpotent
    (X : Matrix (Fin n) (Fin n) R) (hX : IsNilpotent X)
    (p : MvPolynomial (Fin n × Fin n) R) :
    ∃ k : ℕ, ((sourceRegularDifferential X).toLinearMap ^ k)
      (generalLinearRegularPolynomialMap R n p) = 0 := by
  apply sourceDerivation_polynomial_locallyNilpotent
  intro ij
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, ?_⟩
  rw [sourceRegularDifferential_pow_X, hk, map_zero, mul_zero]
  rfl

end
end Dubon2026
