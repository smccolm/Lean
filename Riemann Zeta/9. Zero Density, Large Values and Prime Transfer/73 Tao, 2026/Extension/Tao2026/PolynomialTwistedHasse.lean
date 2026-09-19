import Tao2026.BurgessWeilPrimeKummerLiteralWeilOnly
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Normalized Hasse derivatives for polynomial character fibers

Multiplication by a power of the base polynomial clears all derivative
denominators. The resulting operator is linear with an explicit degree bound.
Frobenius powers are constant for all lower Hasse derivatives at a point.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem polynomial_pow_dvd_mul_hasseDeriv_mul_pow
    {K : Type*} [Field K] (f g : K[X]) (a r : ℕ) :
    g ^ a ∣ g ^ r * hasseDeriv r (f * g ^ a) := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, ← mul_assoc, hasseDeriv_mul, Finset.mul_sum]
      apply Finset.dvd_sum
      intro ij hij
      have hij' : ij.1 + ij.2 = r := Finset.mem_antidiagonal.mp hij
      have hsecond : g ∣ g ^ ij.2 * hasseDeriv ij.2 g := by
        by_cases hj : ij.2 = 0
        · simp [hj]
        · exact dvd_mul_of_dvd_left (dvd_pow_self g hj) _
      have hdiv := mul_dvd_mul (ih ij.1) hsecond
      convert hdiv using 1
      rw [← hij', pow_add]
      ring

def polynomialTwistedHasse
    {K : Type*} [Field K] (f g : K[X]) (a r : ℕ) : K[X] :=
  (g ^ r * hasseDeriv r (f * g ^ a)) / g ^ a

theorem polynomialTwistedHasse_spec
    {K : Type*} [Field K] (f g : K[X]) (hg : g ≠ 0) (a r : ℕ) :
    g ^ a * polynomialTwistedHasse f g a r = g ^ r * hasseDeriv r (f * g ^ a) := by
  exact EuclideanDomain.mul_div_cancel' (pow_ne_zero a hg)
    (polynomial_pow_dvd_mul_hasseDeriv_mul_pow f g a r)

theorem polynomialTwistedHasse_natDegree_le
    {K : Type*} [Field K] (f g : K[X]) (hg : g ≠ 0) (a r : ℕ) :
    (polynomialTwistedHasse f g a r).natDegree ≤ f.natDegree + r * g.natDegree := by
  by_cases hzero : polynomialTwistedHasse f g a r = 0
  · simp [hzero]
  have hdeg := congrArg Polynomial.natDegree (polynomialTwistedHasse_spec f g hg a r)
  rw [natDegree_mul (pow_ne_zero a hg) hzero, natDegree_pow] at hdeg
  have hbound : (g ^ r * hasseDeriv r (f * g ^ a)).natDegree ≤
      r * g.natDegree + (f.natDegree + a * g.natDegree) := by
    calc
      _ ≤ (g ^ r).natDegree + (hasseDeriv r (f * g ^ a)).natDegree := natDegree_mul_le
      _ ≤ r * g.natDegree + (f * g ^ a).natDegree := by
        rw [natDegree_pow]
        exact Nat.add_le_add_left ((natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _)) _
      _ ≤ _ := by
        apply Nat.add_le_add_left
        simpa only [natDegree_pow] using (natDegree_mul_le (p := f) (q := g ^ a))
  omega

def polynomialTwistedHasseLinear
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (a r : ℕ) : K[X] →ₗ[K] K[X] where
  toFun f := polynomialTwistedHasse f g a r
  map_add' f h := by
    apply mul_left_cancel₀ (pow_ne_zero a hg)
    rw [mul_add, polynomialTwistedHasse_spec f g hg a r,
      polynomialTwistedHasse_spec h g hg a r,
      polynomialTwistedHasse_spec (f + h) g hg a r, add_mul, map_add, mul_add]
  map_smul' c f := by
    apply mul_left_cancel₀ (pow_ne_zero a hg)
    change g ^ a * polynomialTwistedHasse (c • f) g a r =
      g ^ a * (c • polynomialTwistedHasse f g a r)
    rw [mul_smul_comm, polynomialTwistedHasse_spec f g hg a r,
      polynomialTwistedHasse_spec (c • f) g hg a r, smul_mul_assoc, map_smul, mul_smul_comm]

theorem polynomial_hasseDeriv_pow_expChar_eval_eq_zero
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (f : K[X]) (n r : ℕ) (hr : 0 < r) (hrQ : r < p ^ n) (x : K) :
    (hasseDeriv r (f ^ p ^ n)).eval x = 0 := by
  rw [← taylor_coeff, taylor_pow, ← map_iterateFrobenius_expand p]
  rw [coeff_map, coeff_expand (expChar_pow_pos K p n)]
  rw [if_neg (Nat.not_dvd_of_pos_of_lt hr hrQ), map_zero]

theorem polynomial_hasseDeriv_mul_pow_expChar_eval
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (f g : K[X]) (n r : ℕ) (hr : r < p ^ n) (x : K) :
    (hasseDeriv r (f * g ^ p ^ n)).eval x =
      (hasseDeriv r f).eval x * g.eval x ^ p ^ n := by
  rw [hasseDeriv_mul, eval_finsetSum]
  rw [Finset.sum_eq_single (r, 0)]
  · simp
  · intro ij hij hne
    have hij' : ij.1 + ij.2 = r := Finset.mem_antidiagonal.mp hij
    have hj : 0 < ij.2 := by
      by_contra hj
      have hj0 : ij.2 = 0 := by omega
      exact hne (Prod.ext (by omega) hj0)
    rw [eval_mul, polynomial_hasseDeriv_pow_expChar_eval_eq_zero p g n ij.2 hj
      (by omega), mul_zero]
  · simp

theorem polynomial_hasseDeriv_mul_X_pow_expChar_eval
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (f : K[X]) (n r k : ℕ) (hr : r < p ^ n) (x : K) (hx : x ^ p ^ n = x) :
    (hasseDeriv r (f * X ^ (p ^ n * k))).eval x =
      (hasseDeriv r f).eval x * x ^ k := by
  rw [mul_comm (p ^ n) k, pow_mul,
    polynomial_hasseDeriv_mul_pow_expChar_eval p f (X ^ k) n r hr]
  simp only [eval_pow, eval_X, pow_right_comm x k (p ^ n), hx]

end
end Tao2026
