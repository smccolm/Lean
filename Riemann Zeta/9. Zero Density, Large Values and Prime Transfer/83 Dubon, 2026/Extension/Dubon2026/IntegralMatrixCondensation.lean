/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Integral reduction input for original unitary arithmetic quotient finiteness

Adapted from TauCetiProject/TauCeti, commit
9fc5d5a87d00cb696e606ccdae66420cc837c05e, under Apache-2.0.
Only the dependency needed for positive definite integral form classes is
ported. The exact open chain is DUB-17 -> integral unitary auxiliary
automorphic modules -> finite original arithmetic double cosets ->
bounded classes of the actual integral trace lattices. The construction,
local comparison and determinant bound for those original lattices remain
separate obligations; this result alone does not close that chain.
-/

namespace Dubon2026

noncomputable section

open Matrix

variable {R : Type*} [CommRing R]

/-- **Chiò's condensation.** For a square matrix `A` of size `n + 1`, the matrix `A'` of `2 × 2`
minors `A 0 0 * A (i + 1) (j + 1) - A (i + 1) 0 * A 0 (j + 1)` satisfies
`A 0 0 · det A' = (A 0 0)ⁿ · det A`. No invertibility of `A 0 0` is needed. -/
theorem matrix_mul_det_condensation_eq_pow_mul_det {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A 0 0 * (of fun i j : Fin n ↦ A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ).det =
      A 0 0 ^ n * A.det := by
  -- Scale the rows below the corner by `A 0 0`, then clear the first column below the corner.
  set s : Fin (n + 1) → R := Fin.cons 1 fun _ ↦ A 0 0
  set c : Fin (n + 1) → R := Fin.cons 0 fun i ↦ A i.succ 0
  set A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) R := of fun i j ↦ s i * A i j
  set A₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) R := of fun i j ↦ A₁ i j - c i * A₁ 0 j
  have h₁ : A₁.det = A 0 0 ^ n * A.det := by
    rw [det_mul_column, Fin.prod_univ_succ]
    simp [s]
  have h₂ : A₁.det = A₂.det :=
    det_eq_of_forall_row_eq_smul_add_const c 0 rfl fun i j ↦ by simp [A₂, c]
  have h₃ : A₂.det = A 0 0 *
      (of fun i j : Fin n ↦ A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero fun i _ ↦ by
      simp [A₂, A₁, s, c, mul_comm]]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, add_zero]
    congr 2
    · simp [A₂, A₁, s, c]
    · ext i j
      simp [A₂, A₁, s, c]
  rw [← h₃, ← h₂, h₁]


end
end Dubon2026
