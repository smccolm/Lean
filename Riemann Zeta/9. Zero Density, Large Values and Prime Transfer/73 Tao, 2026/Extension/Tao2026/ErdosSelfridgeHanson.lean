import Tao2026.ErdosSelfridgeLargeGrowth
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Hanson's elementary primorial mechanism

This file begins the elementary proof of the sole arithmetic input left by
the explicit Erdős--Selfridge Section 3.1 assembly.  It follows Denis Hanson's
Sylvester-sequence construction.  The recurrence starts `2,3,7,43,...`; its
reciprocal sum telescopes strictly below one, and consequently the sum of the
corresponding quotient floors is strictly smaller than the numerator.  This
is the valuation margin used in Hanson's multinomial multiple of the least
common multiple.
-/

namespace Tao2026

open scoped BigOperators Nat

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 8192

/-- Hanson's Sylvester sequence `2,3,7,43,...`. -/
def hansonSylvester : ℕ → ℕ
  | 0 => 2
  | k + 1 => hansonSylvester k * (hansonSylvester k - 1) + 1

@[simp] theorem hansonSylvester_zero : hansonSylvester 0 = 2 := rfl

@[simp] theorem hansonSylvester_succ (k : ℕ) :
    hansonSylvester (k + 1) =
      hansonSylvester k * (hansonSylvester k - 1) + 1 := rfl

theorem two_le_hansonSylvester (k : ℕ) : 2 ≤ hansonSylvester k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [hansonSylvester_succ]
      have hone : 1 ≤ hansonSylvester k - 1 := by omega
      have hprod : 0 < hansonSylvester k * (hansonSylvester k - 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega

theorem hansonSylvester_pos (k : ℕ) : 0 < hansonSylvester k :=
  lt_of_lt_of_le (by omega) (two_le_hansonSylvester k)

theorem hansonSylvester_succ_sub_one (k : ℕ) :
    hansonSylvester (k + 1) - 1 =
      hansonSylvester k * (hansonSylvester k - 1) := by
  rw [hansonSylvester_succ]
  exact Nat.add_sub_cancel _ _

theorem hansonSylvester_lt_succ (k : ℕ) :
    hansonSylvester k < hansonSylvester (k + 1) := by
  rw [hansonSylvester_succ]
  have hk := two_le_hansonSylvester k
  have hone : 1 ≤ hansonSylvester k - 1 := by omega
  have hle : hansonSylvester k ≤
      hansonSylvester k * (hansonSylvester k - 1) := by
    simpa using Nat.mul_le_mul_left (hansonSylvester k) hone
  omega

theorem add_two_le_hansonSylvester (k : ℕ) :
    k + 2 ≤ hansonSylvester k := by
  induction k with
  | zero => simp
  | succ k ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (hansonSylvester_lt_succ k))

/-- Every natural cutoff is passed by an explicit Sylvester-sequence term. -/
theorem lt_hansonSylvester_self_add_one (n : ℕ) :
    n < hansonSylvester (n + 1) := by
  have := add_two_le_hansonSylvester (n + 1)
  omega

/-- The reciprocal recurrence behind the Egyptian-fraction identity. -/
theorem hansonSylvester_reciprocal_step (k : ℕ) :
    (1 : ℚ) / hansonSylvester k =
      1 / ((hansonSylvester k - 1 : ℕ) : ℚ) -
        1 / ((hansonSylvester (k + 1) - 1 : ℕ) : ℚ) := by
  have hk : (hansonSylvester k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hansonSylvester_pos k))
  have hkOne : ((hansonSylvester k - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by have := two_le_hansonSylvester k; omega :
      hansonSylvester k - 1 ≠ 0)
  have hsucc :
      ((hansonSylvester (k + 1) - 1 : ℕ) : ℚ) =
        (hansonSylvester k : ℚ) * ((hansonSylvester k - 1 : ℕ) : ℚ) := by
    exact_mod_cast hansonSylvester_succ_sub_one k
  rw [hsucc]
  have hone : 1 ≤ hansonSylvester k :=
    (by omega : 1 ≤ 2).trans (two_le_hansonSylvester k)
  rw [Nat.cast_sub hone] at hkOne ⊢
  field_simp [hk, hkOne]
  ring

/-- Exact telescoping of the first `k` reciprocal weights. -/
theorem sum_range_hansonSylvester_reciprocal (k : ℕ) :
    ∑ i ∈ Finset.range k, (1 : ℚ) / hansonSylvester i =
      1 - 1 / ((hansonSylvester k - 1 : ℕ) : ℚ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, hansonSylvester_reciprocal_step]
      ring

theorem sum_range_hansonSylvester_reciprocal_lt_one (k : ℕ) :
    ∑ i ∈ Finset.range k, (1 : ℚ) / hansonSylvester i < 1 := by
  rw [sum_range_hansonSylvester_reciprocal]
  have hk : (0 : ℚ) < ((hansonSylvester k - 1 : ℕ) : ℚ) := by
    exact_mod_cast (by have := two_le_hansonSylvester k; omega :
      0 < hansonSylvester k - 1)
  have hinv : (0 : ℚ) < 1 / ((hansonSylvester k - 1 : ℕ) : ℚ) := by positivity
  linarith

private theorem cast_natDiv_le_div (m a : ℕ) (ha : 0 < a) :
    ((m / a : ℕ) : ℚ) ≤ (m : ℚ) / a := by
  rw [le_div_iff₀ (by exact_mod_cast ha)]
  exact_mod_cast Nat.div_mul_le_self m a

/-- Hanson's strict floor-sum lemma for the first `k` Sylvester weights. -/
theorem sum_range_div_hansonSylvester_lt (k m : ℕ) (hm : 0 < m) :
    ∑ i ∈ Finset.range k, m / hansonSylvester i < m := by
  have hterm : ∀ i ∈ Finset.range k,
      (((m / hansonSylvester i : ℕ) : ℚ) ≤
        (m : ℚ) / hansonSylvester i) := by
    intro i _
    exact cast_natDiv_le_div m (hansonSylvester i) (hansonSylvester_pos i)
  have hsum :
      ((∑ i ∈ Finset.range k, m / hansonSylvester i : ℕ) : ℚ) ≤
        ∑ i ∈ Finset.range k, (m : ℚ) / hansonSylvester i := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum hterm
  have hfactor :
      (∑ i ∈ Finset.range k, (m : ℚ) / hansonSylvester i) =
        (m : ℚ) * ∑ i ∈ Finset.range k,
          (1 : ℚ) / hansonSylvester i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrecip := sum_range_hansonSylvester_reciprocal_lt_one k
  have hstrict :
      (∑ i ∈ Finset.range k, (m : ℚ) / hansonSylvester i) < m := by
    rw [hfactor]
    simpa using
      mul_lt_mul_of_pos_left hrecip (by exact_mod_cast hm : (0 : ℚ) < m)
  exact_mod_cast hsum.trans_lt hstrict

/-- With the explicit cutoff `k=n+1`, all later quotient floors vanish and
the active quotient floors still have a strict one-unit margin. -/
theorem sum_range_self_add_one_div_hansonSylvester_lt
    (n m : ℕ) (hm : 0 < m) :
    ∑ i ∈ Finset.range (n + 1), m / hansonSylvester i < m :=
  sum_range_div_hansonSylvester_lt (n + 1) m hm

/-- Product of the factorials of Hanson's quotient floors. -/
def hansonFactorialDenominator (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (n + 1), (n / hansonSylvester i) !

/-- Hanson's integer coefficient. Terms beyond `n+1` would contribute only
`0! = 1`, so this finite definition is the source's infinite product. -/
def hansonCoefficient (n : ℕ) : ℕ :=
  n ! / hansonFactorialDenominator n

theorem sum_range_self_add_one_div_hansonSylvester_le (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), n / hansonSylvester i ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (sum_range_self_add_one_div_hansonSylvester_lt n n
      (Nat.pos_of_ne_zero hn)).le

theorem hansonFactorialDenominator_dvd_factorial (n : ℕ) :
    hansonFactorialDenominator n ∣ n ! := by
  unfold hansonFactorialDenominator
  exact (Nat.prod_factorial_dvd_factorial_sum
    (Finset.range (n + 1)) (fun i => n / hansonSylvester i)).trans
      (Nat.factorial_dvd_factorial
        (sum_range_self_add_one_div_hansonSylvester_le n))

theorem hansonFactorialDenominator_mul_coefficient (n : ℕ) :
    hansonFactorialDenominator n * hansonCoefficient n = n ! := by
  rw [hansonCoefficient]
  exact Nat.mul_div_cancel' (hansonFactorialDenominator_dvd_factorial n)

theorem hansonFactorialDenominator_pos (n : ℕ) :
    0 < hansonFactorialDenominator n := by
  unfold hansonFactorialDenominator
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem hansonCoefficient_pos (n : ℕ) : 0 < hansonCoefficient n := by
  have hspec := hansonFactorialDenominator_mul_coefficient n
  by_contra hzero
  have : hansonCoefficient n = 0 := Nat.eq_zero_of_not_pos hzero
  rw [this, mul_zero] at hspec
  exact Nat.factorial_ne_zero n hspec.symm

/-- Division by a Sylvester denominator commutes with the prime-power
division used in Legendre's formula. -/
theorem div_hansonSylvester_div (n i q : ℕ) :
    (n / hansonSylvester i) / q = (n / q) / hansonSylvester i := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

/-- At every positive quotient layer, Hanson's denominator factorials leave
a strict valuation margin. -/
theorem sum_range_hanson_quotient_layer_lt
    (n q : ℕ) (hq : 0 < n / q) :
    ∑ i ∈ Finset.range (n + 1),
        (n / hansonSylvester i) / q < n / q := by
  simpa only [div_hansonSylvester_div] using
    sum_range_div_hansonSylvester_lt (n + 1) (n / q) hq

/-- The non-strict layer inequality, including the layers above `n`. -/
theorem sum_range_hanson_quotient_layer_le (n q : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n / hansonSylvester i) / q ≤ n / q := by
  by_cases hq : 0 < n / q
  · exact (sum_range_hanson_quotient_layer_lt n q hq).le
  · have hz : n / q = 0 := Nat.eq_zero_of_not_pos hq
    simp only [div_hansonSylvester_div, hz, Nat.zero_div, Finset.sum_const_zero,
      le_refl]

/-- Legendre expansion of the factorial denominator, with the common bound
`n+1` used for every quotient factorial. -/
theorem factorization_hansonFactorialDenominator
    (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (hansonFactorialDenominator n).factorization p =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.Ico 1 (n + 1),
          (n / hansonSylvester i) / p ^ j := by
  unfold hansonFactorialDenominator
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [Nat.factorization_factorial hp]
    exact (Nat.log_le_self p (n / hansonSylvester i)).trans_lt
      (Nat.lt_succ_of_le (Nat.div_le_self n _))
  · intro i _hi
    exact Nat.factorial_ne_zero _

/-- Hanson's floor lemma makes the factorial denominator carry strictly less
`p`-adic valuation than `n!` for every prime `p <= n`. -/
theorem factorization_hansonFactorialDenominator_lt_factorial
    (n : ℕ) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (hansonFactorialDenominator n).factorization p <
      (n !).factorization p := by
  rw [factorization_hansonFactorialDenominator n hp,
    Nat.factorization_factorial hp
      ((Nat.log_le_self p n).trans_lt (Nat.lt_succ_self n))]
  rw [Finset.sum_comm]
  apply Finset.sum_lt_sum
  · intro j _hj
    exact sum_range_hanson_quotient_layer_le n (p ^ j)
  · refine ⟨1, ?_, ?_⟩
    · simp
      have hn : 1 ≤ n := hp.one_le.trans hpn
      omega
    · simp only [pow_one]
      exact sum_range_hanson_quotient_layer_lt n p
        (Nat.div_pos hpn hp.pos)

/-- Every prime at most `n` divides Hanson's coefficient. -/
theorem prime_dvd_hansonCoefficient
    (n : ℕ) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∣ hansonCoefficient n := by
  apply (hp.dvd_iff_one_le_factorization
    (Nat.ne_of_gt (hansonCoefficient_pos n))).2
  have hspec := hansonFactorialDenominator_mul_coefficient n
  have hfacEq := congrArg (fun m : ℕ => m.factorization p) hspec
  dsimp only at hfacEq
  rw [Nat.factorization_mul
      (Nat.ne_of_gt (hansonFactorialDenominator_pos n))
      (Nat.ne_of_gt (hansonCoefficient_pos n)),
    Finsupp.coe_add, Pi.add_apply] at hfacEq
  have hstrict :=
    factorization_hansonFactorialDenominator_lt_factorial n hp hpn
  omega

/-- The product of all primes below `n` divides Hanson's coefficient.  This is
the squarefree portion of Hanson's least-common-multiple divisibility theorem
and is exactly the divisor needed by the Erdős--Selfridge argument. -/
theorem erdosSelfridgePrimeProduct_dvd_hansonCoefficient (n : ℕ) :
    erdosSelfridgePrimeProduct n ∣ hansonCoefficient n := by
  unfold erdosSelfridgePrimeProduct
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primesBelow hp).prime
  · intro p hp
    exact prime_dvd_hansonCoefficient n
      (Nat.prime_of_mem_primesBelow hp) (Nat.lt_of_mem_primesBelow hp).le

/-! ## A fixed four-weight multinomial bound

For the quantitative half it is useful to freeze the first four Sylvester
denominators `2,3,7,43`.  Their reciprocal sum is `1805/1806`.  The residual
part of `n` is kept as a fifth multinomial cell. -/

def hansonFourQuotientSum (n : ℕ) : ℕ :=
  n / 2 + n / 3 + n / 7 + n / 43

def hansonFourRemainder (n : ℕ) : ℕ :=
  n - hansonFourQuotientSum n

def hansonFourParts (n : ℕ) : Fin 5 → ℕ :=
  ![n / 2, n / 3, n / 7, n / 43, hansonFourRemainder n]

def hansonFourWeights : Fin 5 → ℕ :=
  ![903, 602, 258, 42, 1]

def hansonFourMultinomial (n : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (hansonFourParts n)

def hansonFourFactorialDenominator (n : ℕ) : ℕ :=
  ∏ i, (hansonFourParts n i) !

theorem hansonFourQuotientSum_le (n : ℕ) :
    hansonFourQuotientSum n ≤ n := by
  by_cases hn : n = 0
  · simp [hn, hansonFourQuotientSum]
  · have h := sum_range_div_hansonSylvester_lt 4 n (Nat.pos_of_ne_zero hn)
    norm_num [hansonFourQuotientSum, hansonSylvester] at h ⊢
    omega

theorem hansonFourRemainder_le (n : ℕ) : hansonFourRemainder n ≤ n :=
  Nat.sub_le _ _

theorem hansonFourParts_le (n : ℕ) (i : Fin 5) :
    hansonFourParts n i ≤ n := by
  fin_cases i <;>
    simp [hansonFourParts, hansonFourRemainder_le, Nat.div_le_self]

@[simp] theorem sum_hansonFourParts (n : ℕ) :
    ∑ i, hansonFourParts n i = n := by
  simp only [hansonFourParts, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Fin.isValue, Finset.univ_unique, Finset.sum_singleton,
    hansonFourRemainder, hansonFourQuotientSum]
  omega

@[simp] theorem sum_hansonFourWeights :
    ∑ i, hansonFourWeights i = 1806 := by
  decide

theorem hansonFourParts_mem_piAntidiag (n : ℕ) :
    hansonFourParts n ∈ Finset.piAntidiag Finset.univ n := by
  rw [Finset.mem_piAntidiag]
  exact ⟨sum_hansonFourParts n, fun _ _ => Finset.mem_univ _⟩

theorem hansonFourFactorialDenominator_mul_multinomial (n : ℕ) :
    hansonFourFactorialDenominator n * hansonFourMultinomial n = n ! := by
  simpa [hansonFourFactorialDenominator, hansonFourMultinomial,
    sum_hansonFourParts] using
      Nat.multinomial_spec (Finset.univ : Finset (Fin 5)) (hansonFourParts n)

theorem hansonFourFactorialDenominator_pos (n : ℕ) :
    0 < hansonFourFactorialDenominator n := by
  unfold hansonFourFactorialDenominator
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem hansonFourMultinomial_pos (n : ℕ) :
    0 < hansonFourMultinomial n := by
  unfold hansonFourMultinomial
  exact Nat.multinomial_pos _ _

/-- The first four Sylvester quotients retain a strict margin at every
positive quotient layer. -/
theorem hansonFour_quotient_layer_lt (n q : ℕ) (hq : 0 < n / q) :
    (n / 2) / q + (n / 3) / q + (n / 7) / q + (n / 43) / q < n / q := by
  have h := sum_range_div_hansonSylvester_lt 4 (n / q) hq
  norm_num [Finset.sum_range_succ, hansonSylvester] at h
  simpa only [Nat.div_div_eq_div_mul, mul_comm] using h

theorem hansonFour_quotient_layer_le (n q : ℕ) (hq : 0 < q) :
    (n / 2) / q + (n / 3) / q + (n / 7) / q + (n / 43) / q ≤ n / q := by
  by_cases hnq : 0 < n / q
  · exact (hansonFour_quotient_layer_lt n q hnq).le
  · have hnqZero : n / q = 0 := Nat.eq_zero_of_not_pos hnq
    have hnqLt : n < q := by
      rcases Nat.div_eq_zero_iff.mp hnqZero with hzero | hlt
      · exact (Nat.ne_of_gt hq hzero).elim
      · exact hlt
    have h2 : n / 2 < q := (Nat.div_le_self n 2).trans_lt hnqLt
    have h3 : n / 3 < q := (Nat.div_le_self n 3).trans_lt hnqLt
    have h7 : n / 7 < q := (Nat.div_le_self n 7).trans_lt hnqLt
    have h43 : n / 43 < q := (Nat.div_le_self n 43).trans_lt hnqLt
    simp [hnqZero, Nat.div_eq_of_lt h2, Nat.div_eq_of_lt h3,
      Nat.div_eq_of_lt h7, Nat.div_eq_of_lt h43]

theorem sum_hansonFourParts_div_le
    (n q : ℕ) (hq : 0 < q) (hrem : hansonFourRemainder n < q) :
    ∑ i, hansonFourParts n i / q ≤ n / q := by
  have h := hansonFour_quotient_layer_le n q hq
  have hremZero : hansonFourRemainder n / q = 0 := Nat.div_eq_of_lt hrem
  simpa [hansonFourParts, Fin.sum_univ_succ, Matrix.cons_val_succ,
    hremZero, add_assoc] using h

theorem sum_hansonFourParts_div_lt
    (n q : ℕ) (hq : 0 < n / q) (hrem : hansonFourRemainder n < q) :
    ∑ i, hansonFourParts n i / q < n / q := by
  have h := hansonFour_quotient_layer_lt n q hq
  have hremZero : hansonFourRemainder n / q = 0 := Nat.div_eq_of_lt hrem
  simpa [hansonFourParts, Fin.sum_univ_succ, Matrix.cons_val_succ,
    hremZero, add_assoc] using h

/-- Legendre expansion for the denominator of the fixed five-cell
multinomial. -/
theorem factorization_hansonFourFactorialDenominator
    (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (hansonFourFactorialDenominator n).factorization p =
      ∑ i, ∑ j ∈ Finset.Ico 1 (n + 1), hansonFourParts n i / p ^ j := by
  unfold hansonFourFactorialDenominator
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [Nat.factorization_factorial hp]
    exact (Nat.log_le_self p (hansonFourParts n i)).trans_lt
      (Nat.lt_succ_of_le (hansonFourParts_le n i))
  · intro i _hi
    exact Nat.factorial_ne_zero _

theorem factorization_hansonFourFactorialDenominator_lt_factorial
    (n : ℕ) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (hrem : hansonFourRemainder n < p) :
    (hansonFourFactorialDenominator n).factorization p <
      (n !).factorization p := by
  rw [factorization_hansonFourFactorialDenominator n hp,
    Nat.factorization_factorial hp
      ((Nat.log_le_self p n).trans_lt (Nat.lt_succ_self n))]
  rw [Finset.sum_comm]
  apply Finset.sum_lt_sum
  · intro j hj
    have hjOne : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hpPow : p ≤ p ^ j := Nat.le_pow hjOne
    exact sum_hansonFourParts_div_le n (p ^ j) (pow_pos hp.pos j)
      (hrem.trans_le hpPow)
  · refine ⟨1, ?_, ?_⟩
    · simp
      have hn : 1 ≤ n := hp.one_le.trans hpn
      omega
    · simp only [pow_one]
      exact sum_hansonFourParts_div_lt n p
        (Nat.div_pos hpn hp.pos) hrem

/-- A prime larger than the residual cell divides the fixed four-weight
multinomial. -/
theorem prime_dvd_hansonFourMultinomial
    (n : ℕ) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (hrem : hansonFourRemainder n < p) :
    p ∣ hansonFourMultinomial n := by
  apply (hp.dvd_iff_one_le_factorization
    (Nat.ne_of_gt (hansonFourMultinomial_pos n))).2
  have hspec := hansonFourFactorialDenominator_mul_multinomial n
  have hfacEq := congrArg (fun m : ℕ => m.factorization p) hspec
  dsimp only at hfacEq
  rw [Nat.factorization_mul
      (Nat.ne_of_gt (hansonFourFactorialDenominator_pos n))
      (Nat.ne_of_gt (hansonFourMultinomial_pos n)),
    Finsupp.coe_add, Pi.add_apply] at hfacEq
  have hstrict :=
    factorization_hansonFourFactorialDenominator_lt_factorial n hp hpn hrem
  omega

/-- Every prime below `n` is supplied either by the residual primorial or by
the fixed multinomial. -/
theorem erdosSelfridgePrimeProduct_dvd_primorial_remainder_mul_multinomial
    (n : ℕ) :
    erdosSelfridgePrimeProduct n ∣
      primorial (hansonFourRemainder n) * hansonFourMultinomial n := by
  unfold erdosSelfridgePrimeProduct
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primesBelow hp).prime
  · intro p hpMem
    have hp := Nat.prime_of_mem_primesBelow hpMem
    have hpn : p ≤ n := (Nat.lt_of_mem_primesBelow hpMem).le
    by_cases hpr : p ≤ hansonFourRemainder n
    · exact (hp.dvd_primorial_iff.mpr hpr).mul_right _
    · exact (prime_dvd_hansonFourMultinomial n hp hpn
        (Nat.lt_of_not_ge hpr)).mul_left _

theorem erdosSelfridgePrimeProduct_le_primorial_remainder_mul_multinomial
    (n : ℕ) :
    erdosSelfridgePrimeProduct n ≤
      primorial (hansonFourRemainder n) * hansonFourMultinomial n := by
  exact Nat.le_of_dvd
    (Nat.mul_pos (primorial_pos _) (hansonFourMultinomial_pos n))
    (erdosSelfridgePrimeProduct_dvd_primorial_remainder_mul_multinomial n)

/-- The selected multinomial term is bounded by the full weighted expansion
of `1806^n`. -/
theorem hansonFourMultinomial_weighted_le (n : ℕ) :
    hansonFourMultinomial n *
        ∏ i, hansonFourWeights i ^ hansonFourParts n i ≤ 1806 ^ n := by
  rw [← sum_hansonFourWeights, Finset.sum_pow_eq_sum_piAntidiag]
  have hterm := Finset.single_le_sum
    (fun k (_hk : k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 5)) n) =>
      Nat.zero_le (Nat.multinomial Finset.univ k *
        ∏ i ∈ Finset.univ, hansonFourWeights i ^ k i))
    (hansonFourParts_mem_piAntidiag n)
  simpa [hansonFourMultinomial] using hterm

/-- Concrete form of the weighted multinomial estimate. -/
theorem hansonFourMultinomial_weighted_le_explicit (n : ℕ) :
    hansonFourMultinomial n *
        (903 ^ (n / 2) * 602 ^ (n / 3) *
          258 ^ (n / 7) * 42 ^ (n / 43)) ≤ 1806 ^ n := by
  simpa [hansonFourWeights, hansonFourParts, Fin.prod_univ_succ,
    Matrix.cons_val_succ, mul_assoc] using
      hansonFourMultinomial_weighted_le n

/-- The four floor losses, scaled by the common denominator `1806`. -/
theorem hansonFour_floor_two (n : ℕ) :
    903 * n ≤ 1806 * (n / 2) + 903 := by omega

theorem hansonFour_floor_three (n : ℕ) :
    602 * n ≤ 1806 * (n / 3) + 1204 := by omega

theorem hansonFour_floor_seven (n : ℕ) :
    258 * n ≤ 1806 * (n / 7) + 1548 := by omega

theorem hansonFour_floor_fortythree (n : ℕ) :
    42 * n ≤ 1806 * (n / 43) + 1764 := by omega

/-- The residual cell has scaled size at most `n+5419`. -/
theorem hansonFour_remainder_scaled_le (n : ℕ) :
    1806 * hansonFourRemainder n ≤ n + 5419 := by
  have hs := hansonFourQuotientSum_le n
  have h2 := hansonFour_floor_two n
  have h3 := hansonFour_floor_three n
  have h7 := hansonFour_floor_seven n
  have h43 := hansonFour_floor_fortythree n
  simp only [hansonFourRemainder, hansonFourQuotientSum] at hs ⊢
  omega

def hansonFourEntropyNumerator : ℕ :=
  903 ^ 903 * 602 ^ 602 * 258 ^ 258 * 42 ^ 42

def hansonFourFloorLoss : ℕ :=
  903 ^ 903 * 602 ^ 1204 * 258 ^ 1548 * 42 ^ 1764

def hansonFourWeightedFactor (n : ℕ) : ℕ :=
  903 ^ (n / 2) * 602 ^ (n / 3) *
    258 ^ (n / 7) * 42 ^ (n / 43)

/-- Raising to the common denominator clears all four reciprocal exponents;
the right factor records the worst possible loss from the floors. -/
theorem hansonFourEntropyNumerator_pow_le (n : ℕ) :
    hansonFourEntropyNumerator ^ n ≤
      hansonFourFloorLoss * hansonFourWeightedFactor n ^ 1806 := by
  have h2 : 903 ^ (903 * n) ≤
      903 ^ 903 * (903 ^ (n / 2)) ^ 1806 := by
    calc
      903 ^ (903 * n) ≤ 903 ^ (1806 * (n / 2) + 903) :=
        Nat.pow_le_pow_right (by omega) (hansonFour_floor_two n)
      _ = 903 ^ 903 * (903 ^ (n / 2)) ^ 1806 := by
        rw [pow_add, mul_comm]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have h3 : 602 ^ (602 * n) ≤
      602 ^ 1204 * (602 ^ (n / 3)) ^ 1806 := by
    calc
      602 ^ (602 * n) ≤ 602 ^ (1806 * (n / 3) + 1204) :=
        Nat.pow_le_pow_right (by omega) (hansonFour_floor_three n)
      _ = 602 ^ 1204 * (602 ^ (n / 3)) ^ 1806 := by
        rw [pow_add, mul_comm]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have h7 : 258 ^ (258 * n) ≤
      258 ^ 1548 * (258 ^ (n / 7)) ^ 1806 := by
    calc
      258 ^ (258 * n) ≤ 258 ^ (1806 * (n / 7) + 1548) :=
        Nat.pow_le_pow_right (by omega) (hansonFour_floor_seven n)
      _ = 258 ^ 1548 * (258 ^ (n / 7)) ^ 1806 := by
        rw [pow_add, mul_comm]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have h43 : 42 ^ (42 * n) ≤
      42 ^ 1764 * (42 ^ (n / 43)) ^ 1806 := by
    calc
      42 ^ (42 * n) ≤ 42 ^ (1806 * (n / 43) + 1764) :=
        Nat.pow_le_pow_right (by omega) (hansonFour_floor_fortythree n)
      _ = 42 ^ 1764 * (42 ^ (n / 43)) ^ 1806 := by
        rw [pow_add, mul_comm]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h7) h43
  calc
    hansonFourEntropyNumerator ^ n =
        903 ^ (903 * n) * 602 ^ (602 * n) *
          258 ^ (258 * n) * 42 ^ (42 * n) := by
      simp only [hansonFourEntropyNumerator, mul_pow, ← pow_mul]
    _ ≤ (903 ^ 903 * (903 ^ (n / 2)) ^ 1806) *
          (602 ^ 1204 * (602 ^ (n / 3)) ^ 1806) *
          (258 ^ 1548 * (258 ^ (n / 7)) ^ 1806) *
          (42 ^ 1764 * (42 ^ (n / 43)) ^ 1806) := hmul
    _ = hansonFourFloorLoss * hansonFourWeightedFactor n ^ 1806 := by
      simp only [hansonFourFloorLoss, hansonFourWeightedFactor, mul_pow]
      ac_rfl

/-- Integer form of the entropy estimate: no roots, logarithms, or floating
point constants occur. -/
theorem hansonFourMultinomial_pow_mul_entropy_le (n : ℕ) :
    hansonFourMultinomial n ^ 1806 * hansonFourEntropyNumerator ^ n ≤
      hansonFourFloorLoss * 1806 ^ (1806 * n) := by
  have hw : hansonFourMultinomial n * hansonFourWeightedFactor n ≤
      1806 ^ n := by
    simpa only [hansonFourWeightedFactor] using
      hansonFourMultinomial_weighted_le_explicit n
  have hwPow := Nat.pow_le_pow_left hw 1806
  have hentropy := hansonFourEntropyNumerator_pow_le n
  calc
    hansonFourMultinomial n ^ 1806 * hansonFourEntropyNumerator ^ n ≤
        hansonFourMultinomial n ^ 1806 *
          (hansonFourFloorLoss * hansonFourWeightedFactor n ^ 1806) :=
      Nat.mul_le_mul_left _ hentropy
    _ = hansonFourFloorLoss *
        (hansonFourMultinomial n * hansonFourWeightedFactor n) ^ 1806 := by
      rw [mul_pow]
      ac_rfl
    _ ≤ hansonFourFloorLoss * (1806 ^ n) ^ 1806 :=
      Nat.mul_le_mul_left _ hwPow
    _ = hansonFourFloorLoss * 1806 ^ (1806 * n) := by
      rw [← pow_mul]
      congr 2
      omega

def hansonFourRatio : ℕ := 1000000000000

/-- Exact base gap.  After clearing the reciprocal denominator, one step of
the target exponential dominates one trillion steps of the Hanson base. -/
theorem hansonFour_exact_base_gap :
    hansonFourRatio * (3 * 1806 ^ 1806) <
      3 ^ 1806 * hansonFourEntropyNumerator := by
  norm_num [hansonFourRatio, hansonFourEntropyNumerator]

/-- Exact absorption of every floor and residual-primorial loss at the cutoff
`1400`. -/
theorem hansonFour_exact_initial_absorption :
    3 ^ 7225 * hansonFourFloorLoss < hansonFourRatio ^ 1400 := by
  decide

/-- Kernel-checked finite base range for the fixed-weight induction. -/
theorem erdosSelfridgePrimeProduct_mono {m n : ℕ} (hmn : m ≤ n) :
    erdosSelfridgePrimeProduct m ≤ erdosSelfridgePrimeProduct n := by
  by_cases hm : m = 0
  · subst m
    exact erdosSelfridgePrimeProduct_pos n
  · have hmOne : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hnOne : 1 ≤ n := hmOne.trans hmn
    rw [erdosSelfridgePrimeProduct_eq_primorial_sub_one hmOne,
      erdosSelfridgePrimeProduct_eq_primorial_sub_one hnOne]
    exact primorial_mono (Nat.sub_le_sub_right hmn 1)

private theorem erdosSelfridgePrimeProduct_le_three_pow_of_block
    {L U n : ℕ} (hLn : L ≤ n) (hnU : n ≤ U)
    (hcert : erdosSelfridgePrimeProduct U ≤ 3 ^ L) :
    erdosSelfridgePrimeProduct n ≤ 3 ^ n :=
  (erdosSelfridgePrimeProduct_mono hnU).trans
    (hcert.trans (Nat.pow_le_pow_right (by omega) hLn))

theorem erdosSelfridgePrimeProduct_le_three_pow_below_1400
    (n : ℕ) (hn : n < 1400) :
    erdosSelfridgePrimeProduct n ≤ 3 ^ n := by
  by_cases h : n ≤ 2
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 0) (U := 2)
      (Nat.zero_le n) h (by decide)
  by_cases h' : n ≤ 5
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 3) (U := 5) (by omega) h' (by decide)
  by_cases h'' : n ≤ 11
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 6) (U := 11) (by omega) h'' (by decide)
  by_cases h3 : n ≤ 19
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 12) (U := 19) (by omega) h3 (by decide)
  by_cases h4 : n ≤ 29
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 20) (U := 29) (by omega) h4 (by decide)
  by_cases h5 : n ≤ 41
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 30) (U := 41) (by omega) h5 (by decide)
  by_cases h6 : n ≤ 59
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 42) (U := 59) (by omega) h6 (by decide)
  by_cases h7 : n ≤ 79
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 60) (U := 79) (by omega) h7 (by decide)
  by_cases h8 : n ≤ 101
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 80) (U := 101) (by omega) h8 (by decide)
  by_cases h9 : n ≤ 131
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 102) (U := 131) (by omega) h9 (by decide)
  by_cases h10 : n ≤ 163
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 132) (U := 163) (by omega) h10 (by decide)
  by_cases h11 : n ≤ 197
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 164) (U := 197) (by omega) h11 (by decide)
  by_cases h12 : n ≤ 239
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 198) (U := 239) (by omega) h12 (by decide)
  by_cases h13 : n ≤ 281
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 240) (U := 281) (by omega) h13 (by decide)
  by_cases h14 : n ≤ 337
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 282) (U := 337) (by omega) h14 (by decide)
  by_cases h15 : n ≤ 401
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 338) (U := 401) (by omega) h15 (by decide)
  by_cases h16 : n ≤ 463
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 402) (U := 463) (by omega) h16 (by decide)
  by_cases h17 : n ≤ 547
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 464) (U := 547) (by omega) h17 (by decide)
  by_cases h18 : n ≤ 641
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 548) (U := 641) (by omega) h18 (by decide)
  by_cases h19 : n ≤ 739
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 642) (U := 739) (by omega) h19 (by decide)
  by_cases h20 : n ≤ 857
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 740) (U := 857) (by omega) h20 (by decide)
  by_cases h21 : n ≤ 991
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 858) (U := 991) (by omega) h21 (by decide)
  by_cases h22 : n ≤ 1123
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 992) (U := 1123) (by omega) h22 (by decide)
  by_cases h23 : n ≤ 1283
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 1124) (U := 1283) (by omega) h23 (by decide)
  · exact erdosSelfridgePrimeProduct_le_three_pow_of_block (L := 1284) (U := 1399)
      (by omega) (by omega) (by decide)

/-- Hanson's elementary theorem supplies the exact three-primorial proposition
required by the explicit Erdős--Selfridge large-growth argument. -/
theorem erdosSelfridgeThreePrimorialConclusion_hanson :
    ErdosSelfridgeThreePrimorialConclusion := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnSmall : n < 1400
      · exact erdosSelfridgePrimeProduct_le_three_pow_below_1400 n hnSmall
      · have hnLarge : 1400 ≤ n := Nat.le_of_not_gt hnSmall
        let r := hansonFourRemainder n
        let M := hansonFourMultinomial n
        have hrScaled : 1806 * r ≤ n + 5419 := by
          simpa only [r] using hansonFour_remainder_scaled_le n
        have hrSucc : r + 1 < n := by omega
        have hrec := ih (r + 1) hrSucc
        have hprim : primorial r ≤ 3 ^ (r + 1) := by
          have heq := erdosSelfridgePrimeProduct_eq_primorial_sub_one
            (show 1 ≤ r + 1 by omega)
          rw [heq] at hrec
          simpa using hrec
        have hprod : erdosSelfridgePrimeProduct n ≤ primorial r * M := by
          simpa only [r, M] using
            erdosSelfridgePrimeProduct_le_primorial_remainder_mul_multinomial n
        have hmulti : M ^ 1806 * hansonFourEntropyNumerator ^ n ≤
            hansonFourFloorLoss * 1806 ^ (1806 * n) := by
          simpa only [M] using
            hansonFourMultinomial_pow_mul_entropy_le n
        have hrSuccScaled : 1806 * (r + 1) ≤ n + 7225 := by omega
        have hmain :
            erdosSelfridgePrimeProduct n ^ 1806 * hansonFourEntropyNumerator ^ n ≤
              3 ^ (n + 7225) * hansonFourFloorLoss * 1806 ^ (1806 * n) := by
          calc
            erdosSelfridgePrimeProduct n ^ 1806 * hansonFourEntropyNumerator ^ n ≤
                (primorial r * M) ^ 1806 * hansonFourEntropyNumerator ^ n := by
              gcongr
            _ ≤ (3 ^ (r + 1) * M) ^ 1806 * hansonFourEntropyNumerator ^ n := by
              gcongr
            _ = 3 ^ (1806 * (r + 1)) *
                (M ^ 1806 * hansonFourEntropyNumerator ^ n) := by
              rw [mul_pow, ← pow_mul]
              rw [mul_comm (r + 1) 1806]
              simp only [mul_assoc]
            _ ≤ 3 ^ (1806 * (r + 1)) *
                (hansonFourFloorLoss * 1806 ^ (1806 * n)) :=
              Nat.mul_le_mul_left _ hmulti
            _ ≤ 3 ^ (n + 7225) *
                (hansonFourFloorLoss * 1806 ^ (1806 * n)) :=
              Nat.mul_le_mul_right _
                (Nat.pow_le_pow_right (by omega) hrSuccScaled)
            _ = 3 ^ (n + 7225) * hansonFourFloorLoss *
                1806 ^ (1806 * n) := by rw [mul_assoc]
        have hD : 3 ^ 7225 * hansonFourFloorLoss < hansonFourRatio ^ n := by
          calc
            3 ^ 7225 * hansonFourFloorLoss < hansonFourRatio ^ 1400 :=
              hansonFour_exact_initial_absorption
            _ ≤ hansonFourRatio ^ n := Nat.pow_le_pow_right (by
              change 0 < 1000000000000
              norm_num) hnLarge
        have hbase : hansonFourRatio * (3 * 1806 ^ 1806) <
            3 ^ 1806 * hansonFourEntropyNumerator :=
          hansonFour_exact_base_gap
        have hcompare :
            (3 ^ 7225 * hansonFourFloorLoss) * (3 * 1806 ^ 1806) ^ n <
              (3 ^ 1806 * hansonFourEntropyNumerator) ^ n := by
          calc
            (3 ^ 7225 * hansonFourFloorLoss) * (3 * 1806 ^ 1806) ^ n <
                hansonFourRatio ^ n * (3 * 1806 ^ 1806) ^ n := by gcongr
            _ = (hansonFourRatio * (3 * 1806 ^ 1806)) ^ n :=
              (mul_pow hansonFourRatio (3 * 1806 ^ 1806) n).symm
            _ < (3 ^ 1806 * hansonFourEntropyNumerator) ^ n :=
              Nat.pow_lt_pow_left hbase (by omega)
        have hpowered :
            erdosSelfridgePrimeProduct n ^ 1806 * hansonFourEntropyNumerator ^ n <
              (3 ^ n) ^ 1806 * hansonFourEntropyNumerator ^ n := by
          calc
            erdosSelfridgePrimeProduct n ^ 1806 * hansonFourEntropyNumerator ^ n ≤
                3 ^ (n + 7225) * hansonFourFloorLoss *
                  1806 ^ (1806 * n) := hmain
            _ = (3 ^ 7225 * hansonFourFloorLoss) *
                (3 * 1806 ^ 1806) ^ n := by
              have hW : (1806 ^ 1806) ^ n = 1806 ^ (1806 * n) :=
                (pow_mul 1806 1806 n).symm
              rw [pow_add, mul_pow, hW]
              ring
            _ < (3 ^ 1806 * hansonFourEntropyNumerator) ^ n := hcompare
            _ = (3 ^ n) ^ 1806 * hansonFourEntropyNumerator ^ n := by
              simp only [mul_pow, ← pow_mul]
              congr 1
              congr 1
              omega
        have hEpos : 0 < hansonFourEntropyNumerator ^ n := by
          apply pow_pos
          norm_num [hansonFourEntropyNumerator]
        have hpPow : erdosSelfridgePrimeProduct n ^ 1806 < (3 ^ n) ^ 1806 :=
          (Nat.mul_lt_mul_right hEpos).mp hpowered
        exact (lt_of_pow_lt_pow_left' 1806 hpPow).le

/-- The Section 3.1 square conclusion now needs only the Sylvester--Schur
input; Hanson's prime-product bound is internal. -/
theorem erdosSelfridgeSquareConclusion_of_sylvesterSchur
    (hsylvesterSchur : SylvesterSchurConclusion) :
    ErdosSelfridgeSquareConclusion :=
  erdosSelfridgeSquareConclusion_of_sylvesterSchur_of_threePrimorial
    hsylvesterSchur erdosSelfridgeThreePrimorialConclusion_hanson

end Tao2026
