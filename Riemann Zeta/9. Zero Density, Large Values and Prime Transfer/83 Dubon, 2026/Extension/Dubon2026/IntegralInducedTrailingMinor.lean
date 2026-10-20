import Dubon2026.GeneralLinearIntegralInduction

/-! Trailing minors for a nonzero vector in the original dominant-weight
integral induced module. The upper-Borel covariance is proved directly
on the actual matrices over every coefficient ring. These lemmas serve
the remaining source nonzeroness/highest-weight obligation in DUB-17's
integral unitary coefficient chain; they do not assert Hecke nonzeroness.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Left multiplication by an upper-triangular matrix restricts exactly to each actual trailing principal block. -/
theorem upperTriangular_trailing_block_mul (b x : Matrix (Fin n) (Fin n) R)
    (hb : b.BlockTriangular id) (k : Fin n) :
    (b * x).submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val) =
      b.submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val) *
        x.submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val) := by
  ext i j
  change (∑ l : Fin n, b i.val l * x l j.val) =
    ∑ l : {i : Fin n // k ≤ i}, b i.val l.val * x l.val j.val
  apply Finset.sum_congr_set {i : Fin n | k ≤ i}
  · intro l hl
    rfl
  · intro l hl
    rw [hb ((lt_of_not_ge hl).trans_le i.property), zero_mul]

/-- The actual trailing minor transforms by the product of the original Borel diagonal entries in that trailing block. -/
theorem upperTriangular_trailing_minor_mul (b x : Matrix (Fin n) (Fin n) R)
    (hb : b.BlockTriangular id) (k : Fin n) :
    ((b * x).submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).det =
      (∏ i : {i : Fin n // k ≤ i}, b i.val i.val) *
        (x.submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).det := by
  rw [upperTriangular_trailing_block_mul b x hb k, Matrix.det_mul]
  congr 1
  apply Matrix.det_of_upperTriangular
  intro i j hij
  exact hb hij

/-- The original generic trailing minor, as a polynomial over the original coefficient ring. -/
def integralInducedTrailingMinorPolynomial (R : Type*) [CommRing R] (n : ℕ) (k : Fin n) :
    MvPolynomial (Fin n × Fin n) R :=
  ((Matrix.mvPolynomialX (Fin n) (Fin n) R).submatrix
    (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).det

/-- Evaluation of the generic trailing minor is the literal trailing minor of the original matrix. -/
theorem integralInducedTrailingMinorPolynomial_eval
    {A : Type*} [CommRing A] [Algebra R A] (x : Matrix (Fin n) (Fin n) A) (k : Fin n) :
    (MvPolynomial.aeval fun ij : Fin n × Fin n => x ij.1 ij.2)
      (integralInducedTrailingMinorPolynomial R n k) =
      (x.submatrix (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).det := by
  rw [integralInducedTrailingMinorPolynomial, AlgHom.map_det]
  congr 1
  ext i j
  exact MvPolynomial.aeval_X _ _

end
end Dubon2026
