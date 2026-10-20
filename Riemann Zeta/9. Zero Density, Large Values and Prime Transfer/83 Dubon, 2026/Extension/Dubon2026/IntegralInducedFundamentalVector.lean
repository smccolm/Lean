import Dubon2026.IntegralInducedTrailingMinor

/-! Actual nonzero fundamental-weight vectors in the original integral
Borel-induced module. The vector is the original trailing minor regular
function; covariance holds over every coefficient algebra and evaluation
at identity is one. Products and determinant twists will supply general
dominant integral weights on DUB-17's required coefficient chain.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The actual dominant fundamental weight whose reversed Borel character is the trailing diagonal product. -/
def integralInducedFundamentalWeight (k : Fin n) (i : Fin n) : ℤ :=
  if k ≤ i.rev then 1 else 0

/-- The original reversed-weight character is exactly the trailing diagonal product. -/
theorem integralInducedFundamentalWeight_character (k : Fin n) (b : generalLinearBorel R n) :
    generalLinearBorelWeight (integralInducedFundamentalWeight n k) b =
      ∏ i : {i : Fin n // k ≤ i}, generalLinearBorelDiagonalUnit b i.val := by
  change (∏ i : Fin n, generalLinearBorelDiagonalUnit b i ^
    integralInducedFundamentalWeight n k i.rev) = _
  simp only [integralInducedFundamentalWeight, Fin.rev_rev]
  apply Finset.prod_congr_set {i : Fin n | k ≤ i}
  · intro i hi
    change k ≤ i at hi
    simp only [if_pos hi, zpow_one]
  · intro i hi
    change ¬k ≤ i at hi
    simp only [if_neg hi, zpow_zero]

/-- The original trailing minor as a regular function on the original general linear group. -/
def integralInducedFundamentalVector (k : Fin n) : GeneralLinearRegularFunctions R n :=
  generalLinearRegularPolynomialMap R n (integralInducedTrailingMinorPolynomial R n k)

/-- The literal trailing-minor regular function satisfies the exact source covariance over every coefficient algebra. -/
theorem integralInducedFundamentalVector_mem (k : Fin n) :
    integralInducedFundamentalVector R n k ∈
      generalLinearIntegralInducedSubmodule R n (integralInducedFundamentalWeight n k) := by
  intro A _ _ g b
  rw [integralInducedFundamentalVector, generalLinearRegularEval_polynomial,
    generalLinearRegularEval_polynomial, integralInducedTrailingMinorPolynomial_eval,
    integralInducedTrailingMinorPolynomial_eval]
  change ((b.val.val * g.val).submatrix
    (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).det = _
  rw [upperTriangular_trailing_minor_mul b.val.val g.val b.property k,
    integralInducedFundamentalWeight_character]
  simp only [Units.coe_prod, generalLinearBorelDiagonalUnit]

/-- At the original identity matrix, the fundamental vector has value one. -/
theorem integralInducedFundamentalVector_one (k : Fin n) :
    generalLinearRegularEval (1 : GeneralLinearGroup (Fin n) R)
      (integralInducedFundamentalVector R n k) = 1 := by
  rw [integralInducedFundamentalVector, generalLinearRegularEval_polynomial,
    integralInducedTrailingMinorPolynomial_eval]
  have h : (1 : Matrix (Fin n) (Fin n) R).submatrix
      (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val) = 1 := by
    ext i j
    simp [Matrix.one_apply, Subtype.ext_iff]
  change ((1 : Matrix (Fin n) (Fin n) R).submatrix _ _).det = 1
  rw [h, Matrix.det_one]

/-- Every original fundamental-weight integral induced module contains this explicit nonzero regular function. -/
theorem integralInducedFundamentalVector_ne_zero [Nontrivial R] (k : Fin n) :
    integralInducedFundamentalVector R n k ≠ 0 := by
  intro h
  have he := integralInducedFundamentalVector_one R n k
  rw [h, map_zero] at he
  exact zero_ne_one he

end
end Dubon2026
