import GafniTao.WooleyEquation717Tuple
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Finite-degree normal form for Wooley polynomial systems

Wooley Sections 4 and 7 split each polynomial into its coefficients through
degree `k` and a tail divisible by `t^(k+1)`.  This file makes that split
canonical using monic polynomial division.  It is the first exact step toward
the integral linear changes of equations used before (4.6) and (7.7).
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Remainder after division by `X^d`: the coefficients below degree `d`. -/
def wooleyPolynomialLowPart (d : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  f %ₘ (X ^ d)

/-- Quotient after division by `X^d`: the exact high-degree tail. -/
def wooleyPolynomialTail (d : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  f /ₘ (X ^ d)

theorem wooleyPolynomial_low_add_tail
    (d : ℕ) (f : Polynomial ℤ) :
    wooleyPolynomialLowPart d f +
        X ^ d * wooleyPolynomialTail d f = f := by
  exact modByMonic_add_div f (X ^ d)

theorem wooleyPolynomialLowPart_natDegree_lt
    {d : ℕ} (hd : 0 < d) (f : Polynomial ℤ) :
    (wooleyPolynomialLowPart d f).natDegree < d := by
  unfold wooleyPolynomialLowPart
  simpa only [natDegree_X_pow] using
    (natDegree_modByMonic_lt f (monic_X_pow d) (by
      intro h
      have hdeg := congrArg Polynomial.natDegree h
      simp [hd.ne'] at hdeg))

/-- Division by `X^d` does not alter a coefficient below degree `d`. -/
theorem wooleyPolynomialLowPart_coeff
    {d n : ℕ} (hn : n < d) (f : Polynomial ℤ) :
    (wooleyPolynomialLowPart d f).coeff n = f.coeff n := by
  have h := congrArg (fun g : Polynomial ℤ => g.coeff n)
    (wooleyPolynomial_low_add_tail d f)
  simpa only [coeff_add, coeff_X_pow_mul', if_neg (not_le.mpr hn), add_zero]
    using h

/-- Constant coefficient in the canonical degree-`k` low part. -/
def wooleyPolynomialSystemConstant {k : ℕ}
    (phi : WooleyPolynomialSystem k) (j : Fin k) : ℤ :=
  (wooleyPolynomialLowPart (k + 1) (phi j)).coeff 0

/-- The `k×k` matrix of coefficients of `X,...,X^k` in the canonical low
part.  Rows are degrees and columns are source equations. -/
def wooleyPolynomialSystemLowMatrix {k : ℕ}
    (phi : WooleyPolynomialSystem k) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => (wooleyPolynomialLowPart (k + 1) (phi j)).coeff ((i : ℕ) + 1)

/-- The exact polynomial tail beyond degree `k`. -/
def wooleyPolynomialSystemTail {k : ℕ}
    (phi : WooleyPolynomialSystem k) (j : Fin k) : Polynomial ℤ :=
  wooleyPolynomialTail (k + 1) (phi j)

/-- Canonical source-level decomposition into constant, degree `1..k`
coefficient matrix, and an `X^(k+1)` tail. -/
theorem wooleyPolynomialSystem_normalForm {k : ℕ}
    (phi : WooleyPolynomialSystem k) (j : Fin k) :
    phi j =
      C (wooleyPolynomialSystemConstant phi j) +
        ∑ i : Fin k,
          C (wooleyPolynomialSystemLowMatrix phi i j) * X ^ ((i : ℕ) + 1) +
        X ^ (k + 1) * wooleyPolynomialSystemTail phi j := by
  rw [← wooleyPolynomial_low_add_tail (k + 1) (phi j)]
  have hdeg : (wooleyPolynomialLowPart (k + 1) (phi j)).natDegree < k + 1 :=
    wooleyPolynomialLowPart_natDegree_lt (Nat.zero_lt_succ k) (phi j)
  rw [(wooleyPolynomialLowPart (k + 1) (phi j)).as_sum_range_C_mul_X_pow' hdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
  unfold wooleyPolynomialSystemConstant wooleyPolynomialSystemLowMatrix
    wooleyPolynomialSystemTail wooleyPolynomialTail
  ring

/-- For a `p^c`-spaced system the low coefficient matrix is literally
`I + p^c M` over the integers. -/
theorem WooleyPolynomialSystem.Spaced.lowMatrix_eq_identity_add
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c : ℕ}
    (hphi : phi.Spaced p c) :
    ∃ M : Matrix (Fin k) (Fin k) ℤ, ∀ i j,
      wooleyPolynomialSystemLowMatrix phi i j =
        (if i = j then 1 else 0) + (p : ℤ) ^ c * M i j := by
  obtain ⟨psi, hpsi⟩ := hphi
  refine ⟨fun i j => (psi j).coeff ((i : ℕ) + 1), ?_⟩
  intro i j
  unfold wooleyPolynomialSystemLowMatrix
  rw [wooleyPolynomialLowPart_coeff (by omega), hpsi j]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i : ℕ) ≠ (j : ℕ) := by
      exact fun h => hij (Fin.ext h)
    simp [hij, hval]

/-- The constant term of a spaced system is divisible by `p^c`; it cancels
from every equal-length tuple displacement, but its exact shape is recorded. -/
theorem WooleyPolynomialSystem.Spaced.constant_eq_mul
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c : ℕ}
    (hphi : phi.Spaced p c) :
    ∃ d : Fin k → ℤ, ∀ j,
      wooleyPolynomialSystemConstant phi j = (p : ℤ) ^ c * d j := by
  obtain ⟨psi, hpsi⟩ := hphi
  refine ⟨fun j => (psi j).coeff 0, ?_⟩
  intro j
  unfold wooleyPolynomialSystemConstant
  rw [wooleyPolynomialLowPart_coeff (by omega), hpsi j]
  rw [coeff_add, coeff_X_pow]
  have hne : 0 ≠ (j : ℕ) + 1 := by omega
  rw [if_neg hne, coeff_C_mul]
  ring

#print axioms wooleyPolynomial_low_add_tail
#print axioms wooleyPolynomialLowPart_natDegree_lt
#print axioms wooleyPolynomialLowPart_coeff
#print axioms wooleyPolynomialSystem_normalForm
#print axioms WooleyPolynomialSystem.Spaced.lowMatrix_eq_identity_add
#print axioms WooleyPolynomialSystem.Spaced.constant_eq_mul

end

end GafniTao
