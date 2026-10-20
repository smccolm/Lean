/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Adapted for Dubon2026 from mathlib4 commit
4dc3912c3394dbf46f97c6fe75494ae9197b230f, source blob
d7a6e58b5848139da98af23f6d56cd5f982bb827. Module syntax is adapted
and the missing newer determinant-evaluation lemma is proved with the
unchanged native matrix-polynomial API.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# Polynomial identities from evaluation at invertible matrices

We prove `MvPolynomial.eq_of_eval_eq_on_gl`: two polynomials in `MvPolynomial (m × m) k` over an
infinite field `k` are equal if their evaluations agree at every invertible matrix. The proof
uses that the set of invertible matrices is Zariski-dense in `Matrix m m k`.
-/

noncomputable section

namespace MvPolynomial

/-- The native determinant-evaluation identity needed for the upstream density proof. -/
private theorem matrix_det_eval {m k : Type*} [Fintype m] [DecidableEq m] [CommRing k]
    (s : m × m → k) :
    MvPolynomial.eval s (Matrix.det (Matrix.mvPolynomialX m m k)) =
      Matrix.det (Matrix.of fun i j : m => s (i, j)) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply,
    MvPolynomial.eval_X, Matrix.of_apply]

/-- Two polynomials in `MvPolynomial (m × m) k` over an infinite field `k` are equal if their
evaluations agree at every invertible matrix.

The proof considers `(p - q) * det(X)`, where `det(X) := Matrix.det (Matrix.mvPolynomialX m m k)`
is the generic determinant polynomial. Evaluated at any `s : m × m → k`, this product vanishes:
if `det (Matrix.of fun i j => s (i, j)) = 0` the determinant factor kills it; otherwise the
matrix is invertible and the hypothesis applies. By `MvPolynomial.funext` the product is zero,
and since `det(X) ≠ 0` and `MvPolynomial _ k` is an integral domain, `p = q`. -/
theorem eq_of_eval_eq_on_gl {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
    {p q : MvPolynomial (m × m) k}
    (h : ∀ g : Matrix.GeneralLinearGroup m k,
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) p =
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) q) :
    p = q := by
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul, map_sub, map_zero, matrix_det_eval]
    by_cases hs_det : Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hs_det, mul_zero]
    · have hh : (eval s) p = (eval s) q :=
        h (Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.of fun i j : m => s (i, j)) hs_det)
      rw [hh, sub_self, zero_mul]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (Matrix.det_mvPolynomialX_ne_zero m k))

end MvPolynomial
