import Dubon2026.SymmetricDualityInvertible
import Dubon2026.SymmetricDualityTranspose
import Dubon2026.PolarizedSwitch

/-! The original symmetric-power matrices are identified with their
determinant-twisted contragredients by the constructed invertible binomial
matrix. This supplies the actual duality identity required to construct
the CM polarization in DUB-17. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {K : Type*} [Field K]

/-- The literal original symmetric-power representation intertwines with its determinant-twisted dual. -/
theorem symmetricDualityGL_intertwine (n : ℕ) (hn : (n.factorial : K) ≠ 0)
    (g : GeneralLinearGroup (Fin 2) K) :
    homogeneousSymmetricGL n g * symmetricDualityGL n hn =
      GeneralLinearGroup.scalar (Fin (n + 1)) ((GeneralLinearGroup.det g) ^ n) *
        symmetricDualityGL n hn * polarizedContragredient (homogeneousSymmetricGL n g) := by
  let S := homogeneousSymmetricGL n g
  have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) K => A * S.inv.transpose)
    (symmetricDualityMatrix_covariance n g)
  change (S.val * symmetricDualityMatrix n * S.val.transpose) * S.inv.transpose =
    (g.val.det ^ n • symmetricDualityMatrix n) * S.inv.transpose at h
  simp only [mul_assoc, ← Matrix.transpose_mul, S.inv_val, Matrix.transpose_one, mul_one] at h
  apply Units.ext
  change S.val * (symmetricDualityGL n hn).val =
    (Matrix.scalar (Fin (n + 1)) (g.val.det ^ n) * (symmetricDualityGL n hn).val) * S.inv.transpose
  rw [symmetricDualityGL_val, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  exact h

/-- Conjugation by the same original invertible matrix realizes the determinant-twisted contragredient. -/
theorem symmetricDualityGL_conjugate (n : ℕ) (hn : (n.factorial : K) ≠ 0)
    (g : GeneralLinearGroup (Fin 2) K) :
    homogeneousSymmetricGL n g = symmetricDualityGL n hn *
      (GeneralLinearGroup.scalar (Fin (n + 1)) ((GeneralLinearGroup.det g) ^ n) *
        polarizedContragredient (homogeneousSymmetricGL n g)) * (symmetricDualityGL n hn)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  rw [symmetricDualityGL_intertwine]
  have hc := polarizedScalar_commute ((GeneralLinearGroup.det g) ^ n) (symmetricDualityGL n hn)
  rw [hc.eq, mul_assoc]

end
end Dubon2026
