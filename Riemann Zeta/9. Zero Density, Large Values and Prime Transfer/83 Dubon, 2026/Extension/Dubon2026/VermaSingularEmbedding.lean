import Dubon2026.VermaCentralPolynomial

/-! # The actual singular polynomial embedding between reflected Verma weights -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplication by the original singular monomial intertwines the original polynomial lowering operators. -/
theorem vermaSingular_F (n : ℕ) (p : R[X]) :
    vermaPolynomialF (X ^ (n + 1) * p) = X ^ (n + 1) * vermaPolynomialF p := by
  simp only [vermaPolynomialF_apply]
  ring

/-- The original singular monomial shifts the actual Cartan weight from -n-2 to n. -/
theorem vermaSingular_H (n : ℕ) (p : R[X]) :
    vermaPolynomialH (n : R) (X ^ (n + 1) * p) =
      X ^ (n + 1) * vermaPolynomialH (-(n : R) - 2) p := by
  simp only [vermaPolynomialH_apply, derivative_mul, derivative_X_pow_succ]
  simp only [map_sub, map_neg, map_ofNat, map_natCast, map_add, map_one, pow_succ]
  ring

/-- At the actual singular exponent, the original extra raising term vanishes exactly and gives the reflected derivative action. -/
theorem vermaSingular_E (n : ℕ) (p : R[X]) :
    vermaPolynomialE (n : R) (X ^ (n + 1) * p) =
      X ^ (n + 1) * vermaPolynomialE (-(n : R) - 2) p := by
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, pow_one, vermaPolynomialE_apply, map_zero,
        zero_mul, zero_sub, derivative_mul, derivative_X, one_mul, derivative_add,
        neg_zero, map_neg, map_ofNat]
      ring
  | succ n =>
      simp only [vermaPolynomialE_apply, derivative_mul, derivative_add,
        derivative_X_pow_succ, derivative_C, zero_mul, zero_add]
      simp only [map_sub, map_neg, map_ofNat, map_natCast, map_add, map_one,
        Nat.cast_add, Nat.cast_one, pow_succ]
      ring

variable [Algebra ℂ R]

/-- The original singular multiplication intertwines the entire actual compact matrix Lie action at reflected highest weights. -/
theorem vermaSingular_matrix (n : ℕ) (x : ComplexSl2) (p : R[X]) :
    vermaPolynomialLieAction (n : R) x (X ^ (n + 1) * p) =
      X ^ (n + 1) * vermaPolynomialLieAction (-(n : R) - 2) x p := by
  rw [compactSl2_decomposition x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    vermaPolynomialLieAction_H, vermaPolynomialLieAction_E, vermaPolynomialLieAction_F,
    LinearMap.neg_apply, vermaSingular_H, vermaSingular_E, vermaSingular_F,
    mul_add, mul_smul_comm, mul_neg]

/-- The original singular multiplication intertwines every actual enveloping-algebra element at the reflected highest weights. -/
theorem vermaSingular_enveloping (n : ℕ) (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (p : R[X]) :
    vermaPolynomialEnvelopingAction (n : R) z (X ^ (n + 1) * p) =
      X ^ (n + 1) * vermaPolynomialEnvelopingAction (-(n : R) - 2) z p := by
  induction z using universalEnveloping_induction generalizing p with
  | hscalar c =>
      rw [AlgHom.commutes, AlgHom.commutes]
      change c • (X ^ (n + 1) * p) = X ^ (n + 1) * (c • p)
      exact (mul_smul_comm _ _ _).symm
  | hgenerator x =>
      rw [vermaPolynomialEnvelopingAction_generator, vermaPolynomialEnvelopingAction_generator]
      exact vermaSingular_matrix n x p
  | hadd x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, mul_add]
  | hmul x y hx hy => simp only [map_mul, Module.End.mul_apply, hy, hx]

end
end Dubon2026
