import Dubon2026.IntegralPolynomialBorelCovariance
import Dubon2026.IntegralLocalCentralScalar
import Dubon2026.SingularUpperRowElimination
import Dubon2026.ParabolicLastRowQuotient
import Mathlib.Algebra.CharZero.Infinite

/-! Vanishing of the actual induced numerator at singular matrices.
The existing original diagonal lift is reused. Nonzero first-row weight
forces vanishing on a zero first row; the original adjugate upper-Borel
operation extends this to the open singular locus with nonzero cofactor.
This is the numerator-divisibility consumer of the determinant argument.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {A : Type*} [CommRing A] {n : ℕ}

/-- Reuse the already proved original diagonal lift as an element of the literal source upper Borel. -/
def generalLinearBorelSingleDiagonal (a : Fin n) (u : Aˣ) : generalLinearBorel A n :=
  ⟨(parabolicLastRowDiagonal a u).val, Matrix.blockTriangular_diagonal _⟩

/-- The existing diagonal lift retains the same actual unit in its selected coordinate and one elsewhere. -/
theorem generalLinearBorelSingleDiagonal_diagonal (a i : Fin n) (u : Aˣ) :
    generalLinearBorelDiagonalUnit (generalLinearBorelSingleDiagonal a u) i =
      if i = a then u else 1 := by
  apply Units.ext
  change Matrix.diagonal (fun j : Fin n => ((if j = a then u else 1 : Aˣ) : A)) i i = _
  simp

/-- The source reversed-weight character at the original single diagonal lift is its actual selected weight. -/
theorem generalLinearBorelWeight_singleDiagonal (lam : Fin n → ℤ) (a : Fin n) (u : Aˣ) :
    generalLinearBorelWeight lam (generalLinearBorelSingleDiagonal a u) = u ^ lam a.rev := by
  classical
  rw [generalLinearBorelWeight_apply, Finset.prod_eq_single a]
  · rw [generalLinearBorelSingleDiagonal_diagonal]
    simp
  · intro i _ hi
    rw [generalLinearBorelSingleDiagonal_diagonal, if_neg hi, one_zpow]
  · simp

/-- Scaling a zero row by the original diagonal lift leaves the same original matrix unchanged. -/
theorem generalLinearBorelSingleDiagonal_mul_of_row_zero
    (a : Fin n) (u : Aˣ) (M : Matrix (Fin n) (Fin n) A) (hM : ∀ j, M a j = 0) :
    (generalLinearBorelSingleDiagonal a u).val.val * M = M := by
  ext i j
  change (Matrix.diagonal (fun k : Fin n => ((if k = a then u else 1 : Aˣ) : A)) * M) i j = M i j
  rw [Matrix.diagonal_mul]
  by_cases hi : i = a
  · subst i
    simp [hM j]
  · simp [hi]

universe u
variable {R : Type u} [CommRing R]

/-- The exact source polynomial covariance with nonzero selected row weight forces vanishing when that original row is zero. -/
theorem generalLinearIntegralPolynomial_zero_row {n : ℕ}
    (lam : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularPolynomialMap R n P ∈
      generalLinearIntegralInducedSubmodule R n lam)
    (K : Type u) [Field K] [CharZero K] [Algebra R K]
    (a : Fin n) (ha : lam a.rev ≠ 0)
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ j, M a j = 0) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P = 0 := by
  obtain ⟨u, hu⟩ := integralLocal_exists_infinite_order_unit K
  have h := generalLinearIntegralPolynomial_borel_matrix lam P hP K
    (generalLinearBorelSingleDiagonal a u) M
  rw [generalLinearBorelSingleDiagonal_mul_of_row_zero a u M hM,
    generalLinearBorelWeight_singleDiagonal] at h
  have hunit : ((u ^ lam a.rev : Kˣ) : K) - 1 ≠ 0 := by
    intro hz
    have he : u ^ lam a.rev = u ^ (0 : ℤ) := by
      rw [zpow_zero]
      exact Units.ext (sub_eq_zero.mp hz)
    exact ha (hu he)
  apply (mul_eq_zero.mp (show (((u ^ lam a.rev : Kˣ) : K) - 1) *
    MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P = 0 from ?_)).resolve_left hunit
  rw [sub_mul, one_mul, ← h, sub_self]

/-- The original source polynomial vanishes on every singular matrix with nonzero original first diagonal cofactor and nonzero first-row weight. -/
theorem generalLinearIntegralPolynomial_singular_cofactor {n : ℕ}
    (lam : Fin (n + 1) → ℤ) (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R)
    (hP : generalLinearRegularPolynomialMap R (n + 1) P ∈
      generalLinearIntegralInducedSubmodule R (n + 1) lam)
    (K : Type u) [Field K] [CharZero K] [Algebra R K]
    (ha : lam (0 : Fin (n + 1)).rev ≠ 0)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hdet : M.det = 0) (hcofactor : M.adjugate 0 0 ≠ 0) :
    MvPolynomial.aeval (fun ij : Fin (n + 1) × Fin (n + 1) => M ij.1 ij.2) P = 0 := by
  obtain ⟨b, hb, hz⟩ := singularMatrix_exists_upperBorel_firstRow_zero M hdet hcofactor
  have h := generalLinearIntegralPolynomial_borel_matrix lam P hP K b M
  have hchar : generalLinearBorelWeight lam b = 1 := by
    simp only [generalLinearBorelWeight_apply, hb, one_zpow, Finset.prod_const_one]
  rw [hchar, Units.val_one, one_mul] at h
  rw [← h]
  exact generalLinearIntegralPolynomial_zero_row lam P hP K 0 ha (b.val.val * M) hz

end
end Dubon2026
