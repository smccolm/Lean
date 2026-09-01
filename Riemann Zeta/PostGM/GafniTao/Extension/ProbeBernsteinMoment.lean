import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Bernstein

open scoped Polynomial

namespace Probe

noncomputable section

open Polynomial

theorem bernstein_choose_moment (n i : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (Nat.choose k i : ℚ) • bernsteinPolynomial ℚ n k) =
      (Nat.choose n i : ℚ) • (X : ℚ[X]) ^ i := by
  let Y : ℚ[X] := 1 - X
  let P : (ℚ[X])[X] := (X + C Y) ^ n
  have htranslate :
      Polynomial.taylor (X : ℚ[X]) P = (X + 1) ^ n := by
    dsimp [P]
    rw [Polynomial.taylor_pow]
    congr 1
    simp only [map_add, Polynomial.taylor_X, Polynomial.taylor_C]
    dsimp [Y]
    simp only [map_sub, map_one]
    ring
  have htaylor :
      (Polynomial.taylor (X : ℚ[X]) P).coeff i = (Nat.choose n i : ℚ[X]) := by
    rw [htranslate, add_pow]
    simp
    intro h
    simp [Nat.choose_eq_zero_of_lt h]
  rw [Polynomial.taylor_coeff] at htaylor
  have hcalc :
      (Polynomial.hasseDeriv i P).eval (X : ℚ[X]) * X ^ i =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose k i : ℚ[X]) *
            ((Nat.choose n k : ℚ[X]) * X ^ k * Y ^ (n - k)) := by
    dsimp [P]
    rw [add_pow, map_sum]
    change (Polynomial.evalRingHom X) _ * X ^ i = _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hterm :
        ((X : (ℚ[X])[X]) ^ k * C Y ^ (n - k)) *
            (Nat.choose n k : (ℚ[X])[X]) =
          monomial k (Y ^ (n - k) * (Nat.choose n k : ℚ[X])) := by
      rw [← C_mul_X_pow_eq_monomial]
      simp only [← C_pow, ← C_eq_natCast]
      rw [map_mul]
      ac_rfl
    rw [hterm, Polynomial.hasseDeriv_monomial]
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_monomial]
    by_cases hik : i ≤ k
    · calc
        _ = (Nat.choose k i : ℚ[X]) *
              (Y ^ (n - k) * (Nat.choose n k : ℚ[X])) *
                (X ^ (k - i) * X ^ i) := by ring
        _ = _ := by
          rw [← pow_add, Nat.sub_add_cancel hik]
          ring
    · have hki : k < i := Nat.lt_of_not_ge hik
      simp [Nat.choose_eq_zero_of_lt hki]
  rw [htaylor] at hcalc
  simpa [Y, bernsteinPolynomial, Polynomial.smul_eq_C_mul,
    mul_assoc, mul_left_comm, mul_comm] using hcalc.symm

def powerBernsteinCoeff (n i k : ℕ) : ℚ :=
  (Nat.choose k i : ℚ) / (Nat.choose n i : ℚ)

theorem bernstein_power_expansion (n i : ℕ) (hi : i ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (powerBernsteinCoeff n i k) *
          bernsteinPolynomial ℚ n k) =
      (Polynomial.X : ℚ[X]) ^ i := by
  have hchoose : (Nat.choose n i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hi)
  have hm := bernstein_choose_moment n i
  have hm' :
      (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (Nat.choose k i : ℚ) * bernsteinPolynomial ℚ n k) =
        Polynomial.C (Nat.choose n i : ℚ) * (Polynomial.X : ℚ[X]) ^ i := by
    simpa only [Polynomial.smul_eq_C_mul] using hm
  calc
    _ = Polynomial.C ((Nat.choose n i : ℚ)⁻¹) *
        (∑ k ∈ Finset.range (n + 1),
          Polynomial.C (Nat.choose k i : ℚ) * bernsteinPolynomial ℚ n k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_assoc, ← Polynomial.C_mul]
      congr 1
      simp only [powerBernsteinCoeff]
      simp only [div_eq_mul_inv]
      rw [mul_comm]
    _ = Polynomial.C ((Nat.choose n i : ℚ)⁻¹) *
        (Polynomial.C (Nat.choose n i : ℚ) * (Polynomial.X : ℚ[X]) ^ i) := by
      rw [hm']
    _ = (Polynomial.X : ℚ[X]) ^ i := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      field_simp
      simp

def polynomialBernsteinCoeff (n : ℕ) (p : ℚ[X]) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), p.coeff i * powerBernsteinCoeff n i k

def polynomialBernsteinExpansion (n : ℕ) (p : ℚ[X]) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (polynomialBernsteinCoeff n p k) * bernsteinPolynomial ℚ n k

theorem polynomial_eq_bernsteinExpansion
    (n : ℕ) (p : ℚ[X]) (hdegree : p.natDegree ≤ n) :
    p = polynomialBernsteinExpansion n p := by
  have hsum := p.as_sum_range_C_mul_X_pow'
      (n := n + 1) (Nat.lt_succ_of_le hdegree)
  unfold polynomialBernsteinExpansion polynomialBernsteinCoeff
  calc
    p = (∑ i ∈ Finset.range (n + 1), Polynomial.C (p.coeff i) * X ^ i) := hsum
    _ =
        ∑ i ∈ Finset.range (n + 1), Polynomial.C (p.coeff i) *
          (∑ k ∈ Finset.range (n + 1),
            Polynomial.C (powerBernsteinCoeff n i k) *
              bernsteinPolynomial ℚ n k) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [bernstein_power_expansion n i]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          Polynomial.C (p.coeff i * powerBernsteinCoeff n i k) *
            bernsteinPolynomial ℚ n k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_assoc, ← Polynomial.C_mul]
    _ = ∑ k ∈ Finset.range (n + 1),
        ∑ i ∈ Finset.range (n + 1),
          Polynomial.C (p.coeff i * powerBernsteinCoeff n i k) *
            bernsteinPolynomial ℚ n k := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (n + 1),
        Polynomial.C
            (∑ i ∈ Finset.range (n + 1),
              p.coeff i * powerBernsteinCoeff n i k) *
          bernsteinPolynomial ℚ n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_sum, Finset.sum_mul]

theorem coeff_comp_affine (p : ℚ[X]) (left scale : ℚ) (j : ℕ) :
    (p.comp (C left + C scale * X)).coeff j =
      (Polynomial.hasseDeriv j p).eval left * scale ^ j := by
  have hcomp :
      p.comp (C left + C scale * X) =
        (Polynomial.taylor left p).comp (C scale * X) := by
    rw [Polynomial.taylor_apply, Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      ]
    ring
  rw [hcomp, Polynomial.comp_C_mul_X_coeff, Polynomial.taylor_coeff]

theorem hasseDeriv_eval_eq_sum_range
    (n j : ℕ) (p : ℚ[X]) (left : ℚ) (hdegree : p.natDegree ≤ n) :
    (Polynomial.hasseDeriv j p).eval left =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose i j : ℚ) * p.coeff i * left ^ (i - j) := by
  have hsum := p.as_sum_range_C_mul_X_pow'
      (n := n + 1) (Nat.lt_succ_of_le hdegree)
  calc
    _ = (Polynomial.hasseDeriv j
          (∑ i ∈ Finset.range (n + 1), C (p.coeff i) * X ^ i)).eval left := by
      rw [← hsum]
    _ = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose i j : ℚ) * p.coeff i * left ^ (i - j) := by
      rw [map_sum]
      change (Polynomial.evalRingHom left) _ = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [C_mul_X_pow_eq_monomial, Polynomial.hasseDeriv_monomial,
        Polynomial.coe_evalRingHom, Polynomial.eval_monomial]

end

end Probe
