/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted to the exact prime-index polynomials over the required original
coefficient rings from Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Mathlib.Algebra.Polynomial.Monic

/-! # Actual prime-index primitive division polynomials

For the changed prime polynomial X^p+πX, its actual iterates and primitive
quotients have the exact degree, monicity, constant coefficient and
factorization needed to prove the changed torsion point's minimal
polynomial and norm. This is DUB-17's auxiliary normed-uniformizer route;
no formal group or general scalar-endomorphism infrastructure is used.
-/



noncomputable section

open scoped Polynomial



namespace Dubon2026

variable {R : Type*} [CommRing R]

/-- The polynomial `X ^ q + π * X` underlying the standard Lubin--Tate
series. -/
noncomputable def primeChangedPolynomial
    (p : ℕ) (π : R) :
    Polynomial R :=
  Polynomial.X ^ p +
    Polynomial.C π * Polynomial.X

/-- Evaluation of the standard polynomial has the expected two-term
formula. -/
@[simp]
theorem primeChangedPolynomial_eval
    (p : ℕ) (π : R)
    (x : R) :
    (primeChangedPolynomial p π).eval x =
      x ^ p + π * x := by
  simp [primeChangedPolynomial]

/-- The standard Lubin--Tate polynomial has degree `q`. -/
theorem primeChangedPolynomial_natDegree [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) :
    (primeChangedPolynomial p π).natDegree =
      p := by
  rw [primeChangedPolynomial]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow]
    calc
      (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
        simpa only [pow_one] using
          Polynomial.natDegree_C_mul_X_pow_le π 1
      _ < p :=
        (Fact.out : p.Prime).one_lt

/-- The standard Lubin--Tate polynomial is monic. -/
theorem primeChangedPolynomial_monic [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) :
    (primeChangedPolynomial p π).Monic := by
  rw [primeChangedPolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  calc
    (Polynomial.C π * Polynomial.X).degree ≤ 1 :=
      Polynomial.degree_C_mul_X_le π
    _ < (Polynomial.X ^ p :
        Polynomial R).degree := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt

/-- The `n`-fold compositional iterate of the standard polynomial, starting
from `X`. -/
noncomputable def primeChangedPolynomialIterate
    (p : ℕ) (π : R) (n : ℕ) :
    Polynomial R :=
  (primeChangedPolynomial p π).comp^[n] Polynomial.X

/-- The zeroth compositional iterate is `X`. -/
@[simp]
theorem primeChangedPolynomialIterate_zero
    (p : ℕ) (π : R) :
    primeChangedPolynomialIterate p π 0 = Polynomial.X := by
  simp [primeChangedPolynomialIterate]

/-- A successor iterate is obtained by one further composition with the
standard polynomial. -/
theorem primeChangedPolynomialIterate_succ
    (p : ℕ) (π : R) (n : ℕ) :
    primeChangedPolynomialIterate p π (n + 1) =
      (primeChangedPolynomial p π).comp
        (primeChangedPolynomialIterate p π n) := by
  rw [primeChangedPolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- The `n`-fold standard compositional iterate has degree `q ^ n`. -/
theorem primeChangedPolynomialIterate_natDegree [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPolynomialIterate p π n).natDegree =
      p ^ n := by
  rw [primeChangedPolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    primeChangedPolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- Every compositional iterate of the standard polynomial is monic. -/
theorem primeChangedPolynomialIterate_monic [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPolynomialIterate p π n).Monic := by
  induction n with
  | zero =>
      simp [primeChangedPolynomialIterate]
  | succ n ih =>
      rw [primeChangedPolynomialIterate_succ]
      exact (primeChangedPolynomial_monic p π).comp ih
        (by
          rw [primeChangedPolynomialIterate_natDegree]
          exact pow_ne_zero n
            (ne_of_gt
              (Nat.zero_lt_one.trans
                (Fact.out : p.Prime).one_lt)))

/-- Every standard compositional iterate vanishes at zero. -/
@[simp]
theorem primeChangedPolynomialIterate_eval_zero
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPolynomialIterate p π n).eval 0 = 0 := by
  induction n with
  | zero =>
      simp [primeChangedPolynomialIterate]
  | succ n ih =>
      rw [primeChangedPolynomialIterate_succ,
        Polynomial.eval_comp, ih]
      simp [primeChangedPolynomial,
        ne_of_gt
          (Nat.zero_lt_one.trans
            (Fact.out : p.Prime).one_lt)]

/-- The primitive quotient polynomial at level `n + 1`. -/
noncomputable def primeChangedPrimitivePolynomial
    (p : ℕ) (π : R) (n : ℕ) :
    Polynomial R :=
  primeChangedPolynomialIterate p π n ^
      (p - 1) +
    Polynomial.C π

/-- The primitive quotient polynomial has degree `(q - 1) * q ^ n`. -/
theorem primeChangedPrimitivePolynomial_natDegree [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).natDegree =
      (p - 1) *
        p ^ n := by
  rw [primeChangedPrimitivePolynomial]
  have hpos :
      0 < (p - 1) *
        p ^ n :=
    Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Fact.out : p.Prime).one_lt)
      (pow_pos (Fact.out : p.Prime).pos n)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      primeChangedPolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      primeChangedPolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- The primitive quotient polynomial is monic. -/
theorem primeChangedPrimitivePolynomial_monic [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).Monic := by
  rw [primeChangedPrimitivePolynomial]
  let A := primeChangedPolynomialIterate p π n
  have hA : A.Monic :=
    primeChangedPolynomialIterate_monic p π n
  have hmain :
      (A ^ (p - 1)).Monic :=
    hA.pow _
  refine hmain.add_of_left ?_
  calc
    (Polynomial.C π).degree ≤ 0 :=
      Polynomial.degree_C_le
    _ < (A ^ (p - 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hmain.ne_zero,
        Polynomial.natDegree_pow,
        primeChangedPolynomialIterate_natDegree]
      exact_mod_cast Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Fact.out : p.Prime).one_lt)
        (pow_pos (Fact.out : p.Prime).pos n)

/-- The constant coefficient of the primitive quotient polynomial is `π`. -/
@[simp]
theorem primeChangedPrimitivePolynomial_coeff_zero
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).coeff 0 = π := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [primeChangedPrimitivePolynomial,
    primeChangedPolynomialIterate_eval_zero,
    ne_of_gt
      (Nat.sub_pos_of_lt
        (Fact.out : p.Prime).one_lt)]

/-- The next compositional iterate is the current iterate times its primitive
quotient polynomial. -/
theorem primeChangedPolynomialIterate_succ_factor
    (p : ℕ) [Fact p.Prime] (π : R) (n : ℕ) :
    primeChangedPolynomialIterate p π (n + 1) =
      primeChangedPolynomialIterate p π n *
        primeChangedPrimitivePolynomial p π n := by
  have hq : p ≠ 0 :=
    ne_of_gt
      (Nat.zero_lt_one.trans
        (Fact.out : p.Prime).one_lt)
  rw [primeChangedPolynomialIterate_succ,
    primeChangedPolynomial,
    primeChangedPrimitivePolynomial]
  simp only [Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.mul_comp, Polynomial.C_comp]
  rw [← pow_sub_one_mul hq]
  ring

end Dubon2026

end
