import Dubon2026.SourceRegularDifferential
import Dubon2026.GeneralLinearIntegralPolynomialStages
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The actual determinant denominator is fixed by every trace-zero
infinitesimal source action. This permits local nilpotence on original
numerators to descend to the exact determinant localization.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- A trace-zero original infinitesimal matrix has determinant one over the dual numbers. -/
theorem sourceInfinitesimalMatrix_det_of_trace_zero (X : Matrix (Fin n) (Fin n) R)
    (hX : X.trace = 0) :
    (sourceInfinitesimalMatrix X).val.det = 1 := by
  change (1 + (DualNumber.eps : DualNumber R) •
    X.map (algebraMap R (DualNumber R))).det = 1
  rw [Matrix.det_one_add_smul]
  have ht : (X.map (algebraMap R (DualNumber R))).trace = 0 := by
    rw [← AddMonoidHom.map_trace, hX, map_zero]
  simp [ht, pow_two, DualNumber.eps_mul_eps]

/-- The original determinant unit has zero differential under every original trace-zero matrix. -/
theorem sourceRegularDifferential_determinant_zero (X : Matrix (Fin n) (Fin n) R)
    (hX : X.trace = 0) :
    sourceRegularDifferential X
      (generalLinearRegularDeterminantUnit (R := R) (n := n) :
        GeneralLinearRegularFunctions R n) = 0 := by
  let S := GeneralLinearRegularFunctions R n
  have ht : (X.map (algebraMap R S)).trace = 0 := by
    rw [← AddMonoidHom.map_trace, hX, map_zero]
  have he := congrArg (fun z : (DualNumber S)ˣ => (z : DualNumber S))
    (generalLinearRegularEval_determinantUnit (R := R) (n := n) (A := DualNumber S)
      (sourceRegularInfinitesimalPoint X))
  change sourceRegularInfinitesimalEval X
      (generalLinearRegularDeterminantUnit (R := R) (n := n) : S) =
      (sourceRegularInfinitesimalPoint X).val.det at he
  have hd : (sourceRegularInfinitesimalPoint X).val.det =
      TrivSqZeroExt.inl ((generalLinearRegularGeneric R n).val.det) := by
    change ((generalLinearRegularGeneric R n).val.map
      (inlAlgHom R S S) * (sourceInfinitesimalMatrix (X.map (algebraMap R S))).val).det = _
    rw [Matrix.det_mul, sourceInfinitesimalMatrix_det_of_trace_zero _ ht, mul_one]
    exact (AlgHom.map_det (inlAlgHom R S S) _).symm
  change (sourceRegularInfinitesimalEval X
    (generalLinearRegularDeterminantUnit (R := R) (n := n) : S)).snd = 0
  rw [he, hd]
  rfl

/-- Every actual inverse determinant power has zero differential under every original trace-zero matrix. -/
theorem sourceRegularDifferential_inverse_determinant_pow_zero
    (X : Matrix (Fin n) (Fin n) R) (hX : X.trace = 0) (d : ℕ) :
    sourceRegularDifferential X
      (((generalLinearRegularDeterminantUnit (R := R) (n := n) ^ d)⁻¹ :
        (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) = 0 := by
  let D := sourceRegularDifferential X
  have hp : D ((generalLinearRegularDeterminantUnit (R := R) (n := n) ^ d :
      (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) = 0 := by
    rw [Units.val_pow_eq_pow_val, D.leibniz_pow]
    rw [sourceRegularDifferential_determinant_zero X hX, smul_zero]
    exact nsmul_zero d
  rw [D.leibniz_of_mul_eq_one (Units.inv_mul
    (generalLinearRegularDeterminantUnit (R := R) (n := n) ^ d)), hp, smul_zero]

end
end Dubon2026
