import GafniTao.FordLemma51Real
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Ford Section 3: the polynomial Jacobian determinant

This file begins the complete-system argument used in Ford's Theorem 3.  It
proves the basis-independent determinant identity behind Lemma 3.1: an
evaluation matrix for polynomials of successive degrees has determinant equal
to the product of their leading coefficients times the Vandermonde product.
The derivative specialization is the exact algebraic shape needed for Ford's
Jacobian.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Normalize a nonzero polynomial over `ℚ` by its leading coefficient. -/
def fordMonicNormalize (p : ℚ[X]) : ℚ[X] :=
  C p.leadingCoeff⁻¹ * p

theorem fordMonicNormalize_natDegree
    {p : ℚ[X]} (hp : p.leadingCoeff ≠ 0) :
    (fordMonicNormalize p).natDegree = p.natDegree := by
  unfold fordMonicNormalize
  exact natDegree_C_mul (inv_ne_zero hp)

theorem fordMonicNormalize_monic
    {p : ℚ[X]} (hp : p.leadingCoeff ≠ 0) :
    (fordMonicNormalize p).Monic := by
  unfold fordMonicNormalize
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  exact inv_mul_cancel₀ hp

theorem fordMonicNormalize_eval
    (p : ℚ[X]) (x : ℚ) :
    (fordMonicNormalize p).eval x = p.leadingCoeff⁻¹ * p.eval x := by
  simp [fordMonicNormalize]

/-- Determinant of an evaluation matrix for a degree-graded polynomial
basis.  This is the non-monic extension of Mathlib's Vandermonde theorem. -/
theorem ford_det_eval_polynomials
    {n : ℕ} (v : Fin n → ℚ) (p : Fin n → ℚ[X])
    (hdeg : ∀ j, (p j).natDegree = (j : ℕ))
    (hlc : ∀ j, (p j).leadingCoeff ≠ 0) :
    (Matrix.of fun i j => (p j).eval (v i)).det =
      (∏ j, (p j).leadingCoeff) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  let q : Fin n → ℚ[X] := fun j => fordMonicNormalize (p j)
  let A : Matrix (Fin n) (Fin n) ℚ :=
    Matrix.of fun i j => (p j).eval (v i)
  have hqdeg : ∀ j, (q j).natDegree = (j : ℕ) := by
    intro j
    exact (fordMonicNormalize_natDegree (hlc j)).trans (hdeg j)
  have hqmonic : ∀ j, (q j).Monic := fun j =>
    fordMonicNormalize_monic (hlc j)
  have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    v q hqdeg hqmonic
  have hscaled :
      (Matrix.of fun i j => (q j).eval (v i)).det =
        (∏ j, (p j).leadingCoeff⁻¹) * A.det := by
    rw [show (Matrix.of fun i j => (q j).eval (v i)) =
        Matrix.of fun i j => (p j).leadingCoeff⁻¹ * A i j by
      ext i j
      simp only [Matrix.of_apply, A, q, fordMonicNormalize_eval]]
    exact Matrix.det_mul_row (fun j => (p j).leadingCoeff⁻¹) A
  have hcancel :
      (∏ j, (p j).leadingCoeff) *
          (∏ j, (p j).leadingCoeff⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [hlc]
  have hscaledV :
      (∏ j, (p j).leadingCoeff⁻¹) * A.det =
        (Matrix.vandermonde v).det := by
    exact hscaled.symm.trans hV.symm
  change A.det = _
  rw [Matrix.det_vandermonde] at hscaledV
  calc
    A.det = 1 * A.det := by ring
    _ = ((∏ j, (p j).leadingCoeff) *
          (∏ j, (p j).leadingCoeff⁻¹)) * A.det := by rw [hcancel]
    _ = (∏ j, (p j).leadingCoeff) *
          ((∏ j, (p j).leadingCoeff⁻¹) * A.det) := by ring
    _ = (∏ j, (p j).leadingCoeff) *
          ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) := by rw [hscaledV]

theorem ford_derivative_natDegree
    {j : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = j + 1)
    (hlc : p.leadingCoeff ≠ 0) :
    p.derivative.natDegree = j := by
  have hcoeff : p.derivative.coeff j ≠ 0 := by
    rw [coeff_derivative, show p.coeff (j + 1) = p.leadingCoeff by
      rw [← hdeg, coeff_natDegree]]
    exact mul_ne_zero hlc (by positivity)
  apply le_antisymm
  · simpa [hdeg] using natDegree_derivative_le p
  · exact le_natDegree_of_ne_zero hcoeff

theorem ford_derivative_leadingCoeff
    {j : ℕ} {p : ℚ[X]} (hdeg : p.natDegree = j + 1)
    (hlc : p.leadingCoeff ≠ 0) :
    p.derivative.leadingCoeff = p.leadingCoeff * (j + 1 : ℚ) := by
  rw [leadingCoeff, ford_derivative_natDegree hdeg hlc, coeff_derivative,
    show p.coeff (j + 1) = p.leadingCoeff by rw [← hdeg, coeff_natDegree]]

/-- Ford Lemma 3.1 in degree-graded Jacobian form.  Column `j` is the
derivative of a polynomial of degree `j+1`. -/
theorem ford_lemma_3_1_jacobian
    {n : ℕ} (z : Fin n → ℚ) (ψ : Fin n → ℚ[X])
    (hdeg : ∀ j, (ψ j).natDegree = (j : ℕ) + 1)
    (hlc : ∀ j, (ψ j).leadingCoeff ≠ 0) :
    (Matrix.of fun i j => (ψ j).derivative.eval (z i)).det =
      (∏ j, (ψ j).leadingCoeff * ((j : ℕ) + 1 : ℚ)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z j - z i) := by
  have h := ford_det_eval_polynomials z (fun j => (ψ j).derivative)
    (fun j => ford_derivative_natDegree (hdeg j) (hlc j))
    (fun j => by
      rw [ford_derivative_leadingCoeff (hdeg j) (hlc j)]
      exact mul_ne_zero (hlc j) (by positivity))
  have hprod :
      (∏ j, (ψ j).derivative.leadingCoeff) =
        ∏ j, (ψ j).leadingCoeff * ((j : ℕ) + 1 : ℚ) := by
    apply Finset.prod_congr rfl
    intro j _
    exact ford_derivative_leadingCoeff (hdeg j) (hlc j)
  rw [hprod] at h
  exact h

#print axioms fordMonicNormalize_natDegree
#print axioms fordMonicNormalize_monic
#print axioms ford_det_eval_polynomials
#print axioms ford_derivative_natDegree
#print axioms ford_derivative_leadingCoeff
#print axioms ford_lemma_3_1_jacobian

end

end GafniTao
