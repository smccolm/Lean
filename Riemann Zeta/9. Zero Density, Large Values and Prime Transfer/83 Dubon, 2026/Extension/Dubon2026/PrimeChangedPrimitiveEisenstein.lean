/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The quotient-coefficient Eisenstein argument is adapted from
Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/
import Dubon2026.PrimeChangedDivisionPolynomial
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-! # Eisenstein for the actual changed primitive polynomial

Reduction modulo the actual prime uniformizer removes the linear term,
so the iterated primitive polynomial reduces to its leading monomial.
Its constant coefficient is exactly that uniformizer. These facts prove
irreducibility needed to identify the changed point's minimal polynomial
and field norm on DUB-17's ramified reciprocity route.
-/
namespace Dubon2026
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R]

/-- The actual changed iterate reduces to its explicit leading monomial modulo its own uniformizer. -/
theorem primeChangedPolynomialIterate_map_quotient
    (p : ℕ) (π : R) (n : ℕ) :
    (primeChangedPolynomialIterate p π n).map (Ideal.Quotient.mk (Ideal.span {π})) =
      X ^ (p ^ n) := by
  have hπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton π))
  induction n with
  | zero => simp [primeChangedPolynomialIterate]
  | succ n ih =>
    rw [primeChangedPolynomialIterate_succ, Polynomial.map_comp]
    simp [primeChangedPolynomial, ih, hπ, ← pow_mul, pow_succ]

/-- The actual changed primitive polynomial reduces to its leading monomial modulo the actual uniformizer. -/
theorem primeChangedPrimitivePolynomial_map_quotient
    (p : ℕ) (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).map (Ideal.Quotient.mk (Ideal.span {π})) =
      X ^ ((p - 1) * p ^ n) := by
  have hπ : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton π))
  simp [primeChangedPrimitivePolynomial, primeChangedPolynomialIterate_map_quotient,
    hπ, ← pow_mul, Nat.mul_comm]

/-- The actual primitive polynomial is Eisenstein when its displayed uniformizer is prime. -/
theorem primeChangedPrimitivePolynomial_isEisensteinAt [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (hπ : Prime π) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).IsEisensteinAt (Ideal.span {π}) := by
  apply (primeChangedPrimitivePolynomial_monic p π n).isEisensteinAt_of_mem_of_notMem
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).ne_top
  · intro i hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (fun f : Polynomial (R ⧸ Ideal.span {π}) => f.coeff i)
      (primeChangedPrimitivePolynomial_map_quotient p π n)
    simp only [Polynomial.coeff_map] at h
    rw [h]
    rw [primeChangedPrimitivePolynomial_natDegree] at hi
    simp [Polynomial.coeff_X_pow, ne_of_lt hi]
  · rw [primeChangedPrimitivePolynomial_coeff_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have h : ¬π ^ 2 ∣ π ^ 1 := by
      rw [pow_dvd_pow_iff hπ.ne_zero hπ.not_unit]
      omega
    simpa only [pow_one] using h

/-- The exact primitive polynomial is irreducible by the proved Eisenstein criterion. -/
theorem primeChangedPrimitivePolynomial_irreducible [IsDomain R]
    (p : ℕ) [Fact p.Prime] (π : R) (hπ : Prime π) (n : ℕ) :
    Irreducible (primeChangedPrimitivePolynomial p π n) := by
  apply (primeChangedPrimitivePolynomial_isEisensteinAt p π hπ n).irreducible
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ)
    (primeChangedPrimitivePolynomial_monic p π n).isPrimitive
  rw [primeChangedPrimitivePolynomial_natDegree]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)

end
end Dubon2026
