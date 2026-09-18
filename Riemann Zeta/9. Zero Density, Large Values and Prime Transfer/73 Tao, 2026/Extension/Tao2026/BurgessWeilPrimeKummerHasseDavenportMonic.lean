import Tao2026.BurgessWeilPrimeKummerHasseDavenport
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Monic-polynomial coefficient sums for Hasse--Davenport

This file formalizes the first algebraic step in the classical generating-
function proof of Hasse--Davenport.  A monic polynomial is weighted through
its constant and subleading coefficients.  The degree-one coefficient is the
Gauss sum, while every coefficient of degree at least two vanishes when the
multiplicative character is nontrivial.
-/

namespace Tao2026

open scoped BigOperators

noncomputable section

/-- The Hasse--Davenport weight attached to the coefficient vector of a monic
polynomial of degree `n + 1`. -/
def hasseDavenportMonicCoefficientWeight
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (n : ℕ) (c : Fin (n + 1) → K) : ℂ :=
  χ ((-1 : K) ^ (n + 1) * c 0) * ψ (-c (Fin.last n))

/-- Monic polynomials of degree `n` are equivalent to their `n` coefficients
below the leading term. -/
def monicPolynomialEquivCoefficients (K : Type*) [Field K] (n : ℕ) :
    {p : Polynomial K // p.Monic ∧ p.natDegree = n} ≃ (Fin n → K) :=
  (Polynomial.monicEquivDegreeLT n).trans
    (Polynomial.degreeLTEquiv K n).toEquiv

/-- Over a finite field there are finitely many monic polynomials of a fixed
natural degree. -/
noncomputable instance monicPolynomialNatDegreeFintype
    (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    Fintype {p : Polynomial K // p.Monic ∧ p.natDegree = n} :=
  Fintype.ofEquiv (Fin n → K) (monicPolynomialEquivCoefficients K n).symm

/-- The Hasse--Davenport weight written directly in terms of a monic
polynomial of degree `n + 1`. -/
def hasseDavenportMonicPolynomialWeight
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (n : ℕ) (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n + 1}) : ℂ :=
  χ ((-1 : K) ^ (n + 1) * p.1.coeff 0) * ψ (-p.1.coeff n)

/-- The coefficient-vector and polynomial forms of the monic weight agree. -/
theorem hasseDavenportMonicCoefficientWeight_equiv
    {K : Type*} [Field K] (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (n : ℕ) (p : {p : Polynomial K // p.Monic ∧ p.natDegree = n + 1}) :
    hasseDavenportMonicCoefficientWeight χ ψ n
        (monicPolynomialEquivCoefficients K (n + 1) p) =
      hasseDavenportMonicPolynomialWeight χ ψ n p := by
  have hzero : 0 ≠ p.1.natDegree := by rw [p.2.2]; omega
  have hn : n ≠ p.1.natDegree := by rw [p.2.2]; omega
  simp [hasseDavenportMonicCoefficientWeight,
    hasseDavenportMonicPolynomialWeight,
    monicPolynomialEquivCoefficients, Polynomial.monicEquivDegreeLT,
    Polynomial.degreeLTEquiv,
    Polynomial.eraseLead_coeff_of_ne _ hzero,
    Polynomial.eraseLead_coeff_of_ne _ hn]

/-- For a nontrivial multiplicative character, every monic coefficient sum
of degree at least two vanishes. -/
theorem sum_hasseDavenportMonicCoefficientWeight_eq_zero
    {K : Type*} [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ c : Fin (m + 2) → K,
      hasseDavenportMonicCoefficientWeight χ ψ (m + 1) c = 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => K)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [hasseDavenportMonicCoefficientWeight, Fin.consEquiv_apply,
    Fin.cons_zero, Fin.cons_last]
  simp_rw [map_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro y
  calc
    (∑ x : K, χ ((-1 : K) ^ (m + 2)) * χ x *
        ψ (-y (Fin.last m))) =
        (χ ((-1 : K) ^ (m + 2)) * ψ (-y (Fin.last m))) *
          ∑ x : K, χ x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ac_rfl
    _ = 0 := by rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- The degree-one monic coefficient sum is the Gauss sum. -/
theorem sum_hasseDavenportMonicCoefficientWeight_one
    {K : Type*} [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    ∑ c : Fin 1 → K,
      hasseDavenportMonicCoefficientWeight χ ψ 0 c = gaussSum χ ψ := by
  rw [← (Fin.consEquiv (fun _ : Fin 1 => K)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [hasseDavenportMonicCoefficientWeight, Fin.consEquiv_apply,
    Fin.cons_zero, Fintype.sum_unique]
  simpa [neg_one_mul, gaussSum] using
    (Fintype.sum_equiv (Equiv.neg K)
      (fun x : K => χ (-x) * ψ (-x))
      (fun x : K => χ x * ψ x) (fun x => rfl))

/-- Polynomial form of the vanishing of every monic coefficient sum of
degree at least two. -/
theorem sum_hasseDavenportMonicPolynomialWeight_eq_zero
    {K : Type*} [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ p : {p : Polynomial K // p.Monic ∧ p.natDegree = m + 2},
      hasseDavenportMonicPolynomialWeight χ ψ (m + 1) p = 0 := by
  simp_rw [← hasseDavenportMonicCoefficientWeight_equiv]
  rw [(monicPolynomialEquivCoefficients K (m + 2)).sum_comp]
  exact sum_hasseDavenportMonicCoefficientWeight_eq_zero χ ψ hχ m

/-- Polynomial form of the degree-one Gauss-sum identity. -/
theorem sum_hasseDavenportMonicPolynomialWeight_one
    {K : Type*} [Field K] [Fintype K]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    ∑ p : {p : Polynomial K // p.Monic ∧ p.natDegree = 1},
      hasseDavenportMonicPolynomialWeight χ ψ 0 p = gaussSum χ ψ := by
  simp_rw [← hasseDavenportMonicCoefficientWeight_equiv]
  rw [(monicPolynomialEquivCoefficients K 1).sum_comp]
  exact sum_hasseDavenportMonicCoefficientWeight_one χ ψ

end

end Tao2026
