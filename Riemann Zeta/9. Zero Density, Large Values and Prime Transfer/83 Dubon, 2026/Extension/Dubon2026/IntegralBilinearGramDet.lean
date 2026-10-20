/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant

/-! # Integral Gram determinant invariance for the arithmetic lattice class bound

This is the integer-valued specialization of the change-of-basis argument
in TauCeti LinearAlgebra/BilinearMap/GramCongruence, commit
9fc5d5a87d00cb696e606ccdae66420cc837c05e. The pinned bilinear matrix API
already supplies the congruence law, so no general sesquilinear port is
needed. It serves DUB-17's original unitary double-coset finiteness through
the positive integral trace-lattice class bound; the actual lattice bridge
and its determinant bound remain separate obligations.
-/

namespace Dubon2026

noncomputable section

open Matrix Module LinearMap.BilinForm

/-- An integral bilinear form has the same signed Gram determinant in every integral basis. -/
theorem integralBilinForm_gramDet_eq {M ι ι' : Type*} [AddCommGroup M]
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (B : LinearMap.BilinForm ℤ M) (b : Basis ι ℤ M) (b' : Basis ι' ℤ M) :
    (toMatrix b' B).det = (toMatrix b B).det := by
  let c := b.reindex (b.indexEquiv b')
  have hcb : (toMatrix c B).det = (toMatrix b B).det := by
    have he : toMatrix c B = (toMatrix b B).submatrix
        (b.indexEquiv b').symm (b.indexEquiv b').symm := by
      ext i j
      simp [c, toMatrix_apply]
    rw [he, Matrix.det_submatrix_equiv_self]
  have hu : IsUnit ((c.toMatrix b').det) := by
    simpa [Basis.det_apply] using c.isUnit_det b'
  rw [← hcb, ← toMatrix_mul_basis_toMatrix c b' B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  rcases Int.isUnit_eq_one_or hu with h | h <;> rw [h] <;> simp [mul_comm]

end
end Dubon2026
