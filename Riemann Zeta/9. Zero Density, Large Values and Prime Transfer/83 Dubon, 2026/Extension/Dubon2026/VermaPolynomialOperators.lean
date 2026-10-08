import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Ring

/-! # Genuine polynomial Verma operators over an original coefficient ring -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R]

/-- The genuine polynomial Verma lowering generator is multiplication by the original polynomial variable. -/
def vermaPolynomialF : Module.End R R[X] := LinearMap.mulLeft R X

/-- The genuine polynomial Verma Cartan operator has its original highest-weight parameter. -/
def vermaPolynomialH (μ : R) : Module.End R R[X] :=
  μ • LinearMap.id - (2 : R) • (vermaPolynomialF * Polynomial.derivative)

/-- The genuine polynomial Verma raising generator is μD minus XD squared. -/
def vermaPolynomialE (μ : R) : Module.End R R[X] :=
  μ • Polynomial.derivative - vermaPolynomialF * (Polynomial.derivative ^ 2)

/-- The actual multiplication operator retains its literal polynomial action. -/
theorem vermaPolynomialF_apply (p : R[X]) : vermaPolynomialF p = X * p := rfl

/-- The actual Cartan operator retains its literal derivative action. -/
theorem vermaPolynomialH_apply (μ : R) (p : R[X]) :
    vermaPolynomialH μ p = C μ * p - C 2 * X * derivative p := by
  simp only [vermaPolynomialH, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Module.End.mul_apply, vermaPolynomialF_apply, smul_eq_C_mul]
  ring

/-- The actual raising operator retains both original derivatives. -/
theorem vermaPolynomialE_apply (μ : R) (p : R[X]) :
    vermaPolynomialE μ p = C μ * derivative p - X * derivative (derivative p) := by
  simp only [vermaPolynomialE, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, vermaPolynomialF_apply, pow_two, smul_eq_C_mul]

/-- The actual polynomial raising and lowering commutator is exactly the original Cartan operator. -/
theorem vermaPolynomial_E_F (μ : R) :
    vermaPolynomialE μ * vermaPolynomialF - vermaPolynomialF * vermaPolynomialE μ =
      vermaPolynomialH μ := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, vermaPolynomialE_apply,
    vermaPolynomialF_apply, vermaPolynomialH_apply, derivative_mul, derivative_add,
    derivative_X, one_mul, map_ofNat]
  ring

/-- The actual polynomial Cartan and raising commutator has the exact sl2 coefficient two. -/
theorem vermaPolynomial_H_E (μ : R) :
    vermaPolynomialH μ * vermaPolynomialE μ - vermaPolynomialE μ * vermaPolynomialH μ =
      (2 : R) • vermaPolynomialE μ := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    vermaPolynomialE_apply, vermaPolynomialH_apply, derivative_mul, derivative_add,
    derivative_sub, derivative_C, derivative_X, derivative_one, derivative_ofNat, zero_mul, one_mul, zero_add,
    smul_eq_C_mul, map_ofNat]
  ring

/-- The actual polynomial Cartan and lowering commutator has the exact sl2 coefficient minus two. -/
theorem vermaPolynomial_H_F (μ : R) :
    vermaPolynomialH μ * vermaPolynomialF - vermaPolynomialF * vermaPolynomialH μ =
      (-2 : R) • vermaPolynomialF := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    vermaPolynomialF_apply, vermaPolynomialH_apply, derivative_mul, derivative_X,
    one_mul, smul_eq_C_mul, map_neg, map_ofNat]
  ring

/-- The original constant polynomial is a highest-weight vector of the original polynomial Verma action. -/
theorem vermaPolynomial_generator (μ : R) :
    vermaPolynomialH μ 1 = μ • (1 : R[X]) ∧ vermaPolynomialE μ 1 = 0 := by
  simp [vermaPolynomialH_apply, vermaPolynomialE_apply, smul_eq_C_mul]

end
end Dubon2026
