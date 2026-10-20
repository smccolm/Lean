import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # The original last-row parabolic for the auxiliary places

BLGG Sections 3.2 and 3.6 use U0 whose last row modulo the place is
(0,...,0,*), with U1 imposing final entry 1. This is a single residue-unit
quotient, distinct from the preliminary full-torus family. For DUB-17,
the distinguished index is Fin.last; the index-parametric presentation
allows the native block-triangular inverse theorem to be reused directly.
-/

namespace Dubon2026

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Native two-block triangularity is exactly the source's last-row vanishing condition. -/
theorem parabolicLastRow_block_iff (a : ι) (M : Matrix ι ι R) :
    M.BlockTriangular (fun i => if i = a then (1 : ℕ) else 0) ↔
      ∀ j, j ≠ a → M a j = 0 := by
  constructor
  · intro h j hj
    apply h
    simp only [hj, if_false, if_true]
    exact Nat.zero_lt_one
  · intro h i j hij
    by_cases hi : i = a
    · subst i
      apply h j
      intro hj
      subst j
      exact (lt_irrefl _ hij)
    · simp only [hi, if_false] at hij
      exact False.elim (Nat.not_lt_zero _ hij)

/-- The actual invertible matrices with the source's distinguished last-row shape. -/
def parabolicLastRowGroup (R : Type*) [CommRing R] (a : ι) : Subgroup (Matrix ι ι R)ˣ where
  carrier := {M | M.val.BlockTriangular (fun i => if i = a then (1 : ℕ) else 0)}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' hM hN := hM.mul hN
  inv_mem' {M} hM := by
    letI := M.isUnit.invertible
    change (M⁻¹).val.BlockTriangular (fun i => if i = a then (1 : ℕ) else 0)
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hM

/-- Membership retains the literal row condition, not only an abstract parabolic label. -/
theorem parabolicLastRowGroup_mem_iff (a : ι) (M : (Matrix ι ι R)ˣ) :
    M ∈ parabolicLastRowGroup R a ↔ ∀ j, j ≠ a → M.val a j = 0 :=
  parabolicLastRow_block_iff a M.val

/-- Multiplication in the distinguished row uses exactly the final scalar entry. -/
theorem parabolicLastRow_mul_entry (a : ι) (M : parabolicLastRowGroup R a)
    (N : Matrix ι ι R) (j : ι) :
    (M.val.val * N) a j = M.val.val a a * N a j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single a
  · intro b _hb hb
    rw [(parabolicLastRowGroup_mem_iff a M.val).mp M.property b hb, zero_mul]
  · simp

end Dubon2026
