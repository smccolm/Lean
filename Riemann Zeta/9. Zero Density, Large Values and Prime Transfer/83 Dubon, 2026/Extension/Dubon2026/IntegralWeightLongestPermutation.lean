import Dubon2026.IntegralDominantVectorTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! The original longest permutation and its exact Borel reversal.
Native permutation matrices give the actual invertible matrix over every
coefficient ring. Conjugation and transpose turn the source reversed
character into the original highest-weight character. These are the
matrix identities for the highest vector in the literal induced module.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The actual longest permutation matrix, constructed by the native permutation-matrix homomorphism. -/
def integralWeightLongest : GeneralLinearGroup (Fin n) R :=
  (Matrix.permMatrixHom (R := R) (n := Fin n)).toHomUnits Fin.revPerm

/-- The underlying longest matrix is the original reversal permutation matrix. -/
theorem integralWeightLongest_val :
    (integralWeightLongest R n).val = (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix R := rfl

/-- The original longest matrix is its own inverse. -/
theorem integralWeightLongest_mul_self : integralWeightLongest R n * integralWeightLongest R n = 1 := by
  have h : (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [integralWeightLongest, ← map_mul, h, map_one]

/-- Multiplication on the left reverses the original rows. -/
theorem integralWeightLongest_mul (x : Matrix (Fin n) (Fin n) R) :
    (integralWeightLongest R n).val * x = x.submatrix Fin.rev id :=
  PEquiv.toMatrix_toPEquiv_mul Fin.revPerm x

/-- Multiplication on the right reverses the original columns. -/
theorem integralWeightLongest_mul_right (x : Matrix (Fin n) (Fin n) R) :
    x * (integralWeightLongest R n).val = x.submatrix id Fin.rev :=
  PEquiv.mul_toMatrix_toPEquiv x Fin.revPerm

/-- Conjugation by the original longest matrix reverses both actual indices. -/
theorem integralWeightLongest_conjugate (g : GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    (integralWeightLongest R n * g * integralWeightLongest R n).val i j = g.val i.rev j.rev := by
  change (((integralWeightLongest R n).val * g.val) * (integralWeightLongest R n).val) i j = _
  rw [integralWeightLongest_mul, integralWeightLongest_mul_right]
  rfl

/-- Transposed longest conjugation carries an original upper-Borel matrix back to the original upper Borel. -/
def integralWeightLongestBorel (b : generalLinearBorel R n) : generalLinearBorel R n :=
  ⟨integralWeightTranspose (integralWeightLongest R n * b.val * integralWeightLongest R n), by
    intro i j hij
    change (integralWeightLongest R n * b.val * integralWeightLongest R n).val j i = 0
    rw [integralWeightLongest_conjugate]
    exact b.property (Fin.rev_lt_rev.mpr hij)⟩

/-- Every original diagonal unit is reversed by the actual longest Borel transform. -/
theorem integralWeightLongestBorel_diagonal (b : generalLinearBorel R n) (i : Fin n) :
    generalLinearBorelDiagonalUnit (integralWeightLongestBorel R n b) i =
      generalLinearBorelDiagonalUnit b i.rev := by
  apply Units.ext
  exact integralWeightLongest_conjugate R n b.val i i

/-- The exact source reversed-weight character becomes the original highest-weight character under the actual longest Borel transform. -/
theorem integralWeightLongestBorel_character (lam : Fin n → ℤ) (b : generalLinearBorel R n) :
    generalLinearBorelWeight lam (integralWeightLongestBorel R n b) =
      ∏ i : Fin n, generalLinearBorelDiagonalUnit b i ^ lam i := by
  simp only [generalLinearBorelWeight_apply, integralWeightLongestBorel_diagonal]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)

/-- The actual longest permutation matrix commutes with every original coefficient ring map. -/
theorem integralWeightLongest_map {A : Type*} [CommRing A] (f : R →+* A) :
    GeneralLinearGroup.map f (integralWeightLongest R n) = integralWeightLongest A n := by
  apply Units.ext
  ext i j
  change f ((Fin.revPerm : Equiv.Perm (Fin n)).toPEquiv.toMatrix i j) =
    (Fin.revPerm : Equiv.Perm (Fin n)).toPEquiv.toMatrix i j
  simp only [PEquiv.toMatrix_apply]
  split_ifs <;> simp

end
end Dubon2026
