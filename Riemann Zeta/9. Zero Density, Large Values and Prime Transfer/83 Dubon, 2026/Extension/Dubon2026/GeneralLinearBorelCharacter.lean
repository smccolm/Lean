import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Block

/-! The literal upper-triangular Borel and its original integral weight
characters over every coefficient ring. This is Geraghty Section 2.2's
Borel, with the reversed weight w0(lambda) used by the induced module. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The diagonal of a product of original upper-triangular matrices is the product of their original diagonal entries. -/
theorem upperTriangular_mul_diagonal (a b : Matrix (Fin n) (Fin n) R)
    (ha : a.BlockTriangular id) (hb : b.BlockTriangular id) (i : Fin n) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [ha hj, zero_mul]
    · rw [hb hj, mul_zero]
  · simp

/-- The actual source Borel subgroup consists precisely of upper-triangular invertible matrices over the original ring. -/
def generalLinearBorel (R : Type*) [CommRing R] (n : ℕ) :
    Subgroup (GeneralLinearGroup (Fin n) R) where
  carrier g := g.val.BlockTriangular id
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := ha.mul hb
  inv_mem' {g} hg := by
    change (g⁻¹).val.BlockTriangular id
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

/-- Every original diagonal entry of an invertible upper-triangular matrix is a unit with inverse given by the original inverse diagonal. -/
def generalLinearBorelDiagonalUnit (g : generalLinearBorel R n) (i : Fin n) : Rˣ where
  val := g.val.val i i
  inv := (g.val⁻¹).val i i
  val_inv := by
    rw [← upperTriangular_mul_diagonal g.val.val (g.val⁻¹).val g.property
      ((generalLinearBorel R n).inv_mem g.property) i]
    have h := congrArg (fun a : Matrix (Fin n) (Fin n) R => a i i) g.val.val_inv
    simpa only [Matrix.one_apply_eq] using h
  inv_val := by
    rw [mul_comm]
    rw [← upperTriangular_mul_diagonal g.val.val (g.val⁻¹).val g.property
      ((generalLinearBorel R n).inv_mem g.property) i]
    have h := congrArg (fun a : Matrix (Fin n) (Fin n) R => a i i) g.val.val_inv
    simpa only [Matrix.one_apply_eq] using h

/-- The original diagonal projection is a genuine character into units at each coordinate. -/
def generalLinearBorelDiagonal (i : Fin n) : generalLinearBorel R n →* Rˣ where
  toFun g := generalLinearBorelDiagonalUnit g i
  map_one' := by
    apply Units.ext
    change (1 : Matrix (Fin n) (Fin n) R) i i = 1
    simp
  map_mul' g h := by
    apply Units.ext
    exact upperTriangular_mul_diagonal g.val.val h.val.val g.property h.property i

/-- The exact source character w0(lambda) reverses the original weight tuple on the original upper Borel diagonal. -/
def generalLinearBorelWeight (lam : Fin n → ℤ) : generalLinearBorel R n →* Rˣ where
  toFun g := ∏ i : Fin n, generalLinearBorelDiagonal i g ^ lam i.rev
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]

/-- The source weight character has its exact reversed-diagonal formula, including negative integral weights. -/
theorem generalLinearBorelWeight_apply (lam : Fin n → ℤ) (g : generalLinearBorel R n) :
    generalLinearBorelWeight lam g =
      ∏ i : Fin n, generalLinearBorelDiagonalUnit g i ^ lam i.rev := rfl

end
end Dubon2026
