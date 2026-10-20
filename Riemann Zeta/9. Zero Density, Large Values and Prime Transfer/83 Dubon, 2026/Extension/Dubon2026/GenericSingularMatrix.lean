import Dubon2026.GenericDeterminantPrime
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The actual generic singular matrix over the original coefficient ring.
Generic determinant primality gives a domain quotient. Its diagonal
cofactors are nonzero, witnessed by actual singular diagonal matrices.
This is the singular-specialization input to the numerator-divisibility
step of the exact integral induced module's denominator bound.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The original generic determinant defines the original singular-matrix ideal. -/
def genericDeterminantIdeal : Ideal (MvPolynomial (Fin n × Fin n) R) :=
  Ideal.span {Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)}

/-- The actual coordinate ring of original singular matrices is the generic determinant quotient. -/
abbrev GenericSingularCoordinate := MvPolynomial (Fin n × Fin n) R ⧸ genericDeterminantIdeal R n

/-- The original singular-matrix ideal is prime over the original UFD. -/
instance genericDeterminantIdealIsPrime [IsDomain R] [UniqueFactorizationMonoid R] [NeZero n] :
    (genericDeterminantIdeal R n).IsPrime :=
  (Ideal.span_singleton_prime (Matrix.det_mvPolynomialX_ne_zero (Fin n) R)).mpr
    Matrix.prime_det_mvPolynomialX

/-- The actual generic singular coordinate ring is a domain over the original UFD. -/
instance genericSingularCoordinateIsDomain [IsDomain R] [UniqueFactorizationMonoid R] [NeZero n] :
    IsDomain (GenericSingularCoordinate R n) := inferInstance

/-- The original generic matrix with entries in its actual determinant quotient. -/
def genericSingularMatrix : Matrix (Fin n) (Fin n) (GenericSingularCoordinate R n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).map (Ideal.Quotient.mk (genericDeterminantIdeal R n))

/-- The actual generic matrix in the original singular quotient has determinant zero. -/
theorem genericSingularMatrix_det : (genericSingularMatrix R n).det = 0 := by
  rw [genericSingularMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- Evaluation at an original singular matrix factors through the actual determinant quotient. -/
def genericSingularEval (A : Matrix (Fin n) (Fin n) R) (hA : A.det = 0) :
    GenericSingularCoordinate R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ (genericDeterminantIdeal R n)
    (MvPolynomial.aeval fun ij : Fin n × Fin n => A ij.1 ij.2) (by
      intro P hP
      obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hP
      rw [map_mul, AlgHom.map_det, Matrix.mvPolynomialX_mapMatrix_aeval, hA, zero_mul])

/-- Actual singular evaluation recovers the same original matrix. -/
theorem genericSingularEval_matrix (A : Matrix (Fin n) (Fin n) R) (hA : A.det = 0) :
    (genericSingularEval R n A hA).mapMatrix (genericSingularMatrix R n) = A := by
  ext i j
  change MvPolynomial.aeval (fun ij : Fin n × Fin n => A ij.1 ij.2)
    (MvPolynomial.X (i, j)) = A i j
  exact MvPolynomial.aeval_X _ _

/-- The original coefficient ring embeds faithfully into the generic singular coordinate ring. -/
theorem genericSingular_algebraMap_injective [NeZero n] :
    Function.Injective (algebraMap R (GenericSingularCoordinate R n)) := by
  let e := genericSingularEval R n 0 (Matrix.det_zero (by infer_instance))
  intro a b h
  have he := congrArg e h
  simpa only [AlgHom.commutes, Algebra.algebraMap_self] using he

/-- The actual generic singular coordinate ring retains characteristic zero from the original coefficient ring. -/
instance genericSingularCoordinateCharZero [CharZero R] [NeZero n] :
    CharZero (GenericSingularCoordinate R n) where
  cast_injective := by
    intro a b h
    apply Nat.cast_injective (R := R)
    apply genericSingular_algebraMap_injective R n
    simpa only [map_natCast] using h

/-- The original diagonal cofactor survives in the generic singular quotient; the actual diagonal matrix with one zero witnesses this. -/
theorem genericSingularMatrix_diagonal_cofactor_ne_zero [Nontrivial R] (i : Fin n) :
    (genericSingularMatrix R n).adjugate i i ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun j => if j = i then 0 else 1)
  have hA : A.det = 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  let e := genericSingularEval R n A hA
  have he : e ((genericSingularMatrix R n).adjugate i i) = 1 := by
    have hmap := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i i)
      (e.map_adjugate (genericSingularMatrix R n))
    rw [genericSingularEval_matrix] at hmap
    simpa [A, Matrix.adjugate_diagonal] using hmap
  intro h
  rw [h, map_zero] at he
  exact zero_ne_one he

end
end Dubon2026
