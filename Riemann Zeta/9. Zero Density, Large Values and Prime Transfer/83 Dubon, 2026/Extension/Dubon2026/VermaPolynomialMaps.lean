import Dubon2026.VermaPolynomialOperators

/-! # Exact change of coefficients in the original polynomial Verma action -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Changing original coefficients commutes with the actual polynomial lowering action. -/
theorem vermaPolynomial_map_F (φ : R →+* S) (p : R[X]) :
    (vermaPolynomialF p).map φ = vermaPolynomialF (p.map φ) := by
  simp only [vermaPolynomialF_apply, Polynomial.map_mul, Polynomial.map_X]

/-- Changing original coefficients evaluates the highest-weight parameter in the actual Cartan action. -/
theorem vermaPolynomial_map_H (φ : R →+* S) (μ : R) (p : R[X]) :
    (vermaPolynomialH μ p).map φ = vermaPolynomialH (φ μ) (p.map φ) := by
  simp only [vermaPolynomialH_apply, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, map_ofNat, Polynomial.map_ofNat, derivative_map]

/-- Changing original coefficients evaluates the highest-weight parameter in both original derivatives of the raising action. -/
theorem vermaPolynomial_map_E (φ : R →+* S) (μ : R) (p : R[X]) :
    (vermaPolynomialE μ p).map φ = vermaPolynomialE (φ μ) (p.map φ) := by
  simp only [vermaPolynomialE_apply, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, derivative_map]

end
end Dubon2026
