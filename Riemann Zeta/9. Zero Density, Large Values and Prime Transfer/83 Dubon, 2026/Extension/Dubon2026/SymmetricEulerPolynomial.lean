import Dubon2026.SatakeSymmetricTrace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Genuine local symmetric-power Euler polynomials

These are the finite products of the constructed local Hecke eigenvalues.
Their construction and prime coefficient identity require no purity theorem.
-/

namespace Dubon2026

open Polynomial

noncomputable section

/-- The true rank-(r+1) local symmetric-power Euler polynomial of a pair of roots. -/
def symmetricEulerPolynomial (α β : ℂ) (r : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range (r + 1), (1 - C (α ^ i * β ^ (r - i)) * X)

/-- The local polynomial has precisely its product of linear spectral factors. -/
theorem symmetricEulerPolynomial_eval (α β : ℂ) (r : ℕ) (z : ℂ) :
    (symmetricEulerPolynomial α β r).eval z =
      ∏ i ∈ Finset.range (r + 1), (1 - α ^ i * β ^ (r - i) * z) := by
  simp only [symmetricEulerPolynomial, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]

/-- Every actual symmetric-power local polynomial has constant coefficient one. -/
theorem symmetricEulerPolynomial_eval_zero (α β : ℂ) (r : ℕ) :
    (symmetricEulerPolynomial α β r).eval 0 = 1 := by
  simp [symmetricEulerPolynomial_eval]

/-- Differentiating the actual spectral product yields the negative symmetric-power trace at zero. -/
theorem symmetricEulerPolynomial_derivative_zero (α β : ℂ) (r : ℕ) :
    (symmetricEulerPolynomial α β r).derivative.eval 0 = -satakeSymmetricTrace α β r := by
  simp [symmetricEulerPolynomial, derivative_prod_finset, eval_finsetSum, eval_prod,
    satakeSymmetricTrace, Finset.sum_neg_distrib]

/-- The first coefficient of the genuine symmetric-power local polynomial is minus its exact trace. -/
theorem symmetricEulerPolynomial_coeff_one (α β : ℂ) (r : ℕ) :
    (symmetricEulerPolynomial α β r).coeff 1 = -satakeSymmetricTrace α β r := by
  simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using
    symmetricEulerPolynomial_derivative_zero α β r

/-- Unit spectral parameters make the actual local polynomial nonvanishing throughout the open unit disc. -/
theorem symmetricEulerPolynomial_ne_zero {α β z : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hz : ‖z‖ < 1) (r : ℕ) : (symmetricEulerPolynomial α β r).eval z ≠ 0 := by
  rw [symmetricEulerPolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ he
  have ht := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_mul, norm_pow, hα, hβ, one_pow, one_mul] at ht
  linarith

/-- The reciprocal of the actual symmetric-power Euler polynomial has its trace as derivative at zero. -/
theorem symmetricEulerPolynomial_inverse_hasDerivAt (α β : ℂ) (r : ℕ) :
    HasDerivAt (fun z : ℂ => ((symmetricEulerPolynomial α β r).eval z)⁻¹)
      (satakeSymmetricTrace α β r) 0 := by
  have he := ((symmetricEulerPolynomial α β r).hasDerivAt 0).inv
    (by rw [symmetricEulerPolynomial_eval_zero]; exact one_ne_zero)
  simpa only [symmetricEulerPolynomial_derivative_zero, symmetricEulerPolynomial_eval_zero,
    neg_neg, one_pow, div_one] using he

/-- Degree one of the actual symmetric-power family recovers the normalized quadratic Euler polynomial. -/
theorem symmetricEulerPolynomial_one_eval (α β z : ℂ) :
    (symmetricEulerPolynomial α β 1).eval z = 1 - (α + β) * z + α * β * z ^ 2 := by
  simp [symmetricEulerPolynomial_eval, Finset.prod_range_succ]
  ring

/-- The genuine primitive form supplies its own unramified symmetric-power local polynomial. -/
def primitiveSymmetricEulerPolynomial {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p r : ℕ) : ℂ[X] :=
  symmetricEulerPolynomial (primitiveSatakePlus f p) (primitiveSatakeMinus f p) r

/-- The true primitive prime-power coefficient is the first coefficient of its actual local symmetric-power Euler factor. -/
theorem primitiveSymmetricEulerPolynomial_coeff_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    (primitiveSymmetricEulerPolynomial f p r).coeff 1 =
      -normalizedCuspCoefficients f.toCuspForm (p ^ r) := by
  rw [primitiveSymmetricEulerPolynomial, symmetricEulerPolynomial_coeff_one,
    primitive_primePower_eq_satakeTrace f hp hpQ]

/-- The actual prime-power coefficient is the first Taylor coefficient of its own reciprocal symmetric-power Euler polynomial. -/
theorem primitiveSymmetricEulerPolynomial_inverse_hasDerivAt {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    HasDerivAt (fun z : ℂ => ((primitiveSymmetricEulerPolynomial f p r).eval z)⁻¹)
      (normalizedCuspCoefficients f.toCuspForm (p ^ r)) 0 := by
  rw [primitive_primePower_eq_satakeTrace f hp hpQ]
  exact symmetricEulerPolynomial_inverse_hasDerivAt _ _ r

end
end Dubon2026
