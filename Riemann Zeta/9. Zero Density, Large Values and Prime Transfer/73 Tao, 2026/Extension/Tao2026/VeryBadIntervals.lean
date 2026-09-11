import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.PrimeCounting
import PrimeNumberTheoremAnd.Consequences
import Tao2026.PrimeIntervals
import Tao2026.PowerfulNumbers

/-!
# Elementary restrictions on very bad intervals

This module begins the source-faithful proof of Tao's Lemma 3.1.
-/

namespace Tao2026

open Filter
open scoped BigOperators

/-- Standard binomial-coefficient form of the Sylvester--Schur theorem. -/
def BinomialSylvesterSchurConclusion : Prop :=
  ∀ (n i : ℕ), 1 ≤ i → i ≤ n / 2 →
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ n.choose i

/-- Exact source contract for the Sylvester--Schur theorem: when `N > H`,
the product of `N+1, ..., N+H` has a prime factor exceeding `H`. -/
def SylvesterSchurConclusion : Prop :=
  ∀ {N H : ℕ}, 1 ≤ H → H < N →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- The strictly weaker Sylvester--Schur window sufficient for Tao's scale
bound: a large prime is needed only when `H² > 2N`. -/
def QuadraticWindowSylvesterSchurConclusion : Prop :=
  ∀ {N H : ℕ}, 1 ≤ H → H < N → 2 * N < H ^ 2 →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- The standard binomial form of Sylvester--Schur implies the exact
consecutive-product form used in Tao's proof. -/
theorem sylvesterSchurConclusion_of_binomial
    (hSS : BinomialSylvesterSchurConclusion) : SylvesterSchurConclusion := by
  intro N H hH hHltN
  have hhalf : H ≤ (N + H) / 2 := by omega
  obtain ⟨p, hp, hHltp, hpChoose⟩ := hSS (N + H) H hH hhalf
  refine ⟨p, hp, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- If every prime factor of a binomial coefficient is at most `k`, its size
is bounded by one factor `n` for each prime below `k+1`. -/
theorem choose_le_pow_card_primesBelow_of_prime_factors_le
    {n k : ℕ} (hk : k ≤ n) (hn : 0 < n)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ n.choose k → p ≤ k) :
    n.choose k ≤ n ^ (k + 1).primesBelow.card := by
  classical
  let support : Finset ℕ :=
    (Finset.range (n + 1)).filter fun p => p.Prime ∧ p ≤ k
  have hsRange : support ⊆ Finset.range (n + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hproduct :
      (∏ p ∈ Finset.range (n + 1),
          p ^ (n.choose k).factorization p) =
        ∏ p ∈ support, p ^ (n.choose k).factorization p := by
    symm
    refine Finset.prod_subset hsRange ?_
    intro p hpRange hpOutside
    have hpFactorization : (n.choose k).factorization p = 0 := by
      by_contra hpos
      have hpPrime : p.Prime := by
        by_contra hpNotPrime
        exact hpos (Nat.factorization_eq_zero_of_not_prime (n.choose k) hpNotPrime)
      have hpDvd : p ∣ n.choose k := Nat.dvd_of_factorization_pos hpos
      exact hpOutside (Finset.mem_filter.mpr ⟨hpRange, hpPrime, hsmall p hpPrime hpDvd⟩)
    simp [hpFactorization]
  have hsPrimes : support ⊆ (k + 1).primesBelow := by
    intro p hp
    have hpData := (Finset.mem_filter.mp hp).2
    exact Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_iff.mpr hpData.2, hpData.1⟩
  calc
    n.choose k =
        ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p :=
      (Nat.prod_pow_factorization_choose n k hk).symm
    _ = ∏ p ∈ support, p ^ (n.choose k).factorization p := hproduct
    _ ≤ ∏ _p ∈ support, n := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact Nat.pow_factorization_choose_le hn
    _ = n ^ support.card := by simp
    _ ≤ n ^ (k + 1).primesBelow.card :=
      Nat.pow_le_pow_right hn (Finset.card_le_card hsPrimes)

/-- A binomial coefficient exceeding the small-prime factorization bound has
a prime factor strictly larger than its lower index. -/
theorem exists_large_prime_dvd_choose_of_pow_card_lt
    {n k : ℕ} (hk : k ≤ n) (hn : 0 < n)
    (hlarge : n ^ (k + 1).primesBelow.card < n.choose k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  by_contra hnone
  have hsmall : ∀ p : ℕ, p.Prime → p ∣ n.choose k → p ≤ k := by
    intro p hpPrime hpDvd
    by_contra hnot
    exact hnone ⟨p, hpPrime, Nat.lt_of_not_ge hnot, hpDvd⟩
  exact (not_lt_of_ge
    (choose_le_pow_card_primesBelow_of_prime_factors_le hk hn hsmall)) hlarge

/-- Elementary lower bound for binomial coefficients, in an integral form
that avoids division: `n^k ≤ choose n k * k^k`. -/
theorem pow_le_choose_mul_pow {n k : ℕ} (hk : k ≤ n) :
    n ^ k ≤ n.choose k * k ^ k := by
  have hproducts :
      n ^ k * k.factorial ≤ k ^ k * n.descFactorial k := by
    calc
      n ^ k * k.factorial =
          (∏ i ∈ Finset.range k, n) *
            ∏ i ∈ Finset.range k, (k - i) := by
        simp [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
      _ = ∏ i ∈ Finset.range k, n * (k - i) := by
        rw [Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ Finset.range k, k * (n - i) := by
        refine Finset.prod_le_prod' ?_
        intro i hi
        have hik : i ≤ k := (Finset.mem_range.mp hi).le
        have hin : i ≤ n := hik.trans hk
        calc
          n * (k - i) = n * k - n * i := by rw [Nat.mul_sub_left_distrib]
          _ ≤ k * n - k * i := by
            rw [Nat.mul_comm n k]
            exact Nat.sub_le_sub_left (Nat.mul_le_mul_right i hk) (k * n)
          _ = k * (n - i) := by rw [Nat.mul_sub_left_distrib]
      _ = (∏ _i ∈ Finset.range k, k) *
          ∏ i ∈ Finset.range k, (n - i) := by
        rw [Finset.prod_mul_distrib]
      _ = k ^ k * n.descFactorial k := by
        simp [Nat.descFactorial_eq_prod_range]
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hproducts
  have hcancel :
      n ^ k * k.factorial ≤ (n.choose k * k ^ k) * k.factorial := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hproducts
  exact Nat.le_of_mul_le_mul_right hcancel (Nat.factorial_pos k)

/-- A central-binomial lower bound remains valid when the upper binomial
index is increased. -/
theorem four_pow_lt_mul_choose_of_two_mul_le
    {n k : ℕ} (hk : 4 ≤ k) (hkn : 2 * k ≤ n) :
    4 ^ k < k * n.choose k := by
  calc
    4 ^ k < k * k.centralBinom := Nat.four_pow_lt_mul_centralBinom k hk
    _ ≤ k * n.choose k := Nat.mul_le_mul_left k (Nat.choose_le_choose k hkn)

/-- A convenient eventual `1.1 H/log H` upper bound for the prime-counting
function, extracted from the frozen prime number theorem. -/
theorem eventually_primeCounting_le_eleven_tenths :
    ∀ᶠ H : ℕ in atTop,
      (H.primeCounting : ℝ) ≤ (11 / 10 : ℝ) * H / Real.log H := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  simp only [div_one] at hc
  have hcNat : Tendsto (fun H : ℕ => c (H : ℝ)) atTop (nhds 0) :=
    hc.comp tendsto_natCast_atTop_atTop
  have hsmall :
      ∀ᶠ H : ℕ in atTop, |c (H : ℝ)| < (1 / 10 : ℝ) := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_atTop.1 hcNat (1 / 10 : ℝ) (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with H hcH hH
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast hH)
  have hcUpper : 1 + c (H : ℝ) ≤ (11 / 10 : ℝ) := by
    have : c (H : ℝ) ≤ 1 / 10 := (le_abs_self _).trans hcH.le
    linarith
  calc
    (H.primeCounting : ℝ) =
        (1 + c (H : ℝ)) * H / Real.log H := by
      simpa using hpi (H : ℝ)
    _ ≤ (11 / 10 : ℝ) * H / Real.log H := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcUpper (Nat.cast_nonneg H)) hlog.le

/-- The numerical logarithmic margin used in both halves of the quadratic
window argument. -/
theorem eleven_tenths_lt_log_four : (11 / 10 : ℝ) < Real.log 4 := by
  calc
    (11 / 10 : ℝ) < 2 * 0.6931471803 := by norm_num
    _ < 2 * Real.log 2 :=
      mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)
    _ = Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring

/-- Eventually the PNT coefficient and both elementary logarithmic error
terms fit below the central-binomial exponent `log 4`. -/
theorem eventually_quadraticWindow_log_margin :
    ∀ᶠ H : ℕ in atTop,
      Real.log H / H + (11 / 10 : ℝ) *
        (1 + Real.log 4 / Real.log H) < Real.log 4 := by
  have hlogDivReal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogDivNat :
      Tendsto (fun H : ℕ => Real.log H / H) atTop (nhds 0) :=
    hlogDivReal.comp tendsto_natCast_atTop_atTop
  have hconstDivNat :
      Tendsto (fun H : ℕ => Real.log 4 / Real.log H) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop
      (Real.log 4)
  have hlimit :
      Tendsto
        (fun H : ℕ => Real.log H / H + (11 / 10 : ℝ) *
          (1 + Real.log 4 / Real.log H)) atTop (nhds (11 / 10 : ℝ)) := by
    simpa only [zero_add, add_zero, mul_one] using
      hlogDivNat.add
        (((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hconstDivNat).const_mul
            (11 / 10 : ℝ))
  exact hlimit.eventually_lt_const eleven_tenths_lt_log_four

/-- Convert a strict logarithmic comparison into an inequality between two
products of natural powers. -/
theorem nat_pow_mul_pow_lt_pow_of_log_lt
    {a b c r s t : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hlog : (r : ℝ) * Real.log a + (s : ℝ) * Real.log b <
      (t : ℝ) * Real.log c) :
    a ^ r * b ^ s < c ^ t := by
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have hbReal : (0 : ℝ) < b := by exact_mod_cast hb
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hc
  have hreal :
      (a : ℝ) ^ r * (b : ℝ) ^ s < (c : ℝ) ^ t := by
    rw [← Real.log_lt_log_iff
      (mul_pos (pow_pos haReal r) (pow_pos hbReal s)) (pow_pos hcReal t),
      Real.log_mul (pow_ne_zero r haReal.ne') (pow_ne_zero s hbReal.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow]
    exact hlog
  exact_mod_cast hreal

/-- Cardinality of primes below `H+1` in the notation used by the
factorization envelope. -/
theorem card_primesBelow_succ_eq_primeCounting (H : ℕ) :
    (H + 1).primesBelow.card = H.primeCounting := by
  simpa [Nat.primesLE] using Nat.primesLE_card_eq_primeCounting H

/-- Uniformly in the quadratic window `2N < H²`, the binomial coefficient
eventually exceeds the complete small-prime factorization envelope. -/
theorem eventually_quadraticWindow_choose_growth :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ, H < N → 2 * N < H ^ 2 →
      (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H := by
  filter_upwards [eventually_primeCounting_le_eleven_tenths,
    eventually_quadraticWindow_log_margin,
    eventually_ge_atTop (4 : ℕ)] with H hpi hmargin hH N hHN hwindow
  let A : ℝ := Real.log (N + H)
  let L : ℝ := Real.log H
  have hHPos : 0 < H := by omega
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hHPos
  have hLPos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hsumPos : 0 < N + H := by omega
  have hsumReal : (0 : ℝ) < N + H := by exact_mod_cast hsumPos
  have hANonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + H by omega))
  have hpi' :
      (H.primeCounting : ℝ) ≤ (11 / 10 : ℝ) * H / L := by
    simpa [L] using hpi
  have hcoefNonneg : 0 ≤ (11 / 10 : ℝ) * H / L := by positivity
  have hmarginMul :
      L + (11 / 10 : ℝ) * H * (1 + Real.log 4 / L) <
        H * Real.log 4 := by
    have hm := mul_lt_mul_of_pos_right hmargin hHReal
    dsimp [L] at hm ⊢
    convert hm using 1 <;> field_simp
  rw [card_primesBelow_succ_eq_primeCounting]
  by_cases hnear : N ≤ 3 * H
  · have hsumLe : N + H ≤ 4 * H := by omega
    have hALe : A ≤ Real.log 4 + L := by
      calc
        A ≤ Real.log ((4 : ℕ) * H) := by
          apply Real.strictMonoOn_log.monotoneOn
          · exact Set.mem_Ioi.mpr hsumReal
          · exact Set.mem_Ioi.mpr (mul_pos (by norm_num) hHReal)
          · exact_mod_cast hsumLe
        _ = Real.log 4 + L := by
          dsimp [L]
          rw [Real.log_mul (by norm_num) hHReal.ne']
    have hpiA :
        (H.primeCounting : ℝ) * A ≤
          (11 / 10 : ℝ) * H * (1 + Real.log 4 / L) := by
      calc
        (H.primeCounting : ℝ) * A ≤
            ((11 / 10 : ℝ) * H / L) * A :=
          mul_le_mul_of_nonneg_right hpi' hANonneg
        _ ≤ ((11 / 10 : ℝ) * H / L) * (Real.log 4 + L) :=
          mul_le_mul_of_nonneg_left hALe hcoefNonneg
        _ = (11 / 10 : ℝ) * H * (1 + Real.log 4 / L) := by
          field_simp
          ring
    have hlogNear :
        (H.primeCounting : ℝ) * A + (1 : ℝ) * L <
          (H : ℝ) * Real.log 4 := by
      linarith
    have hpow :
        (N + H) ^ H.primeCounting * H ^ 1 < 4 ^ H :=
      nat_pow_mul_pow_lt_pow_of_log_lt hsumPos hHPos (by norm_num) (by
        simpa [A, L] using hlogNear)
    have hcentral : 4 ^ H < H * (N + H).choose H :=
      four_pow_lt_mul_choose_of_two_mul_le hH (by omega)
    apply (Nat.mul_lt_mul_left hHPos).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.trans hcentral
  · have hfar : 3 * H < N := Nat.lt_of_not_ge hnear
    have hsumGe : 4 * H ≤ N + H := by omega
    have hlogFourAdd : Real.log 4 + L ≤ A := by
      calc
        Real.log 4 + L = Real.log ((4 : ℕ) * H) := by
          dsimp [L]
          rw [Real.log_mul (by norm_num) hHReal.ne']
        _ ≤ A := by
          dsimp [A]
          apply Real.strictMonoOn_log.monotoneOn
          · exact Set.mem_Ioi.mpr (mul_pos (by norm_num) hHReal)
          · exact Set.mem_Ioi.mpr hsumReal
          · exact_mod_cast hsumGe
    have hbase :
        (11 / 10 : ℝ) * (1 + Real.log 4 / L) < Real.log 4 := by
      have hnonneg : 0 ≤ L / H := by positivity
      have hmargin' :
          L / H + (11 / 10 : ℝ) * (1 + Real.log 4 / L) <
            Real.log 4 := by simpa [L] using hmargin
      linarith
    have hlogFourLeL : Real.log 4 ≤ L := by
      dsimp [L]
      apply Real.strictMonoOn_log.monotoneOn
      · norm_num
      · exact Set.mem_Ioi.mpr hHReal
      · exact_mod_cast hH
    have hslope : 0 ≤ 1 - (11 / 10 : ℝ) / L := by
      rw [sub_nonneg, div_le_one hLPos]
      exact eleven_tenths_lt_log_four.le.trans hlogFourLeL
    have hy : Real.log 4 ≤ A - L := by linarith
    have hbase' :
        (11 / 10 : ℝ) < (1 - (11 / 10 : ℝ) / L) * Real.log 4 := by
      calc
        (11 / 10 : ℝ) < Real.log 4 -
            (11 / 10 : ℝ) * (Real.log 4 / L) := by linarith
        _ = (1 - (11 / 10 : ℝ) / L) * Real.log 4 := by ring
    have hdynamic :
        (11 / 10 : ℝ) * (1 + (A - L) / L) < A - L := by
      have hgrow :
          (11 / 10 : ℝ) < (1 - (11 / 10 : ℝ) / L) * (A - L) :=
        hbase'.trans_le (mul_le_mul_of_nonneg_left hy hslope)
      calc
        (11 / 10 : ℝ) * (1 + (A - L) / L) =
            (11 / 10 : ℝ) + ((11 / 10 : ℝ) / L) * (A - L) := by ring
        _ < (1 - (11 / 10 : ℝ) / L) * (A - L) +
            ((11 / 10 : ℝ) / L) * (A - L) :=
          by simpa [add_comm] using
            add_lt_add_right hgrow (((11 / 10 : ℝ) / L) * (A - L))
        _ = A - L := by ring
    have hpiA :
        (H.primeCounting : ℝ) * A < (H : ℝ) * (A - L) := by
      calc
        (H.primeCounting : ℝ) * A ≤
            ((11 / 10 : ℝ) * H / L) * A :=
          mul_le_mul_of_nonneg_right hpi' hANonneg
        _ = (H : ℝ) * ((11 / 10 : ℝ) * (1 + (A - L) / L)) := by
          field_simp
          ring
        _ < (H : ℝ) * (A - L) :=
          mul_lt_mul_of_pos_left hdynamic hHReal
    have hlogFar :
        (H.primeCounting : ℝ) * A + (H : ℝ) * L <
          (H : ℝ) * A := by linarith
    have hpow :
        (N + H) ^ H.primeCounting * H ^ H < (N + H) ^ H :=
      nat_pow_mul_pow_lt_pow_of_log_lt hsumPos hHPos hsumPos (by
        simpa [A, L] using hlogFar)
    have hlower :
        (N + H) ^ H ≤ (N + H).choose H * H ^ H :=
      pow_le_choose_mul_pow (by omega)
    exact Nat.lt_of_mul_lt_mul_right (hpow.trans_le hlower)

/-- The large prime required in Tao's quadratic window exists uniformly for
all starts once the interval length is sufficiently large. -/
theorem eventually_exists_large_prime_dvd_consecutiveProduct_quadraticWindow :
    ∀ᶠ H : ℕ in atTop, ∀ N : ℕ, H < N → 2 * N < H ^ 2 →
      ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  filter_upwards [eventually_quadraticWindow_choose_growth] with H hgrowth N hHN hwindow
  have hsumPos : 0 < N + H := by omega
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_pow_card_lt
      (show H ≤ N + H by omega) hsumPos (hgrowth N hHN hwindow)
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- It is enough to prove the standard binomial lower bound against the
small-prime factorization envelope. -/
theorem binomialSylvesterSchurConclusion_of_choose_growth
    (hgrowth : ∀ (n i : ℕ), 1 ≤ i → i ≤ n / 2 →
      n ^ (i + 1).primesBelow.card < n.choose i) :
    BinomialSylvesterSchurConclusion := by
  intro n i hi hhalf
  have hin : i ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hn : 0 < n := by omega
  exact exists_large_prime_dvd_choose_of_pow_card_lt hin hn
    (hgrowth n i hi hhalf)

/-- In Tao's quadratic window, the corresponding binomial growth inequality
already supplies every large prime needed by Lemma 3.1. -/
theorem quadraticWindowSylvesterSchurConclusion_of_choose_growth
    (hgrowth : ∀ (N H : ℕ), 1 ≤ H → H < N → 2 * N < H ^ 2 →
      (N + H) ^ (H + 1).primesBelow.card < (N + H).choose H) :
    QuadraticWindowSylvesterSchurConclusion := by
  intro N H hH hHltN hwindow
  have hHN : H ≤ N + H := Nat.le_add_left H N
  have hsum : 0 < N + H := by omega
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_pow_card_lt hHN hsum
      (hgrowth N H hH hHltN hwindow)
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

theorem prime_dvd_consecutiveProduct_exactly_once
    {N H p : ℕ} (hp : p.Prime) (hNltp : N < p)
    (hpLe : p ≤ N + H) (hsumLt : N + H < 2 * p) :
    p ∣ consecutiveProduct N H ∧ ¬p ^ 2 ∣ consecutiveProduct N H := by
  have hpMem : p ∈ consecutiveInterval N H := by
    simpa [consecutiveInterval] using ⟨hNltp, hpLe⟩
  let remainder := ((consecutiveInterval N H).erase p).prod id
  have hproduct : consecutiveProduct N H = p * remainder := by
    rw [consecutiveProduct]
    change (∏ x ∈ consecutiveInterval N H, x) =
      p * ((consecutiveInterval N H).erase p).prod id
    exact (Finset.mul_prod_erase (consecutiveInterval N H) id hpMem).symm
  have hpNotDvdRemainder : ¬p ∣ remainder := by
    change ¬p ∣ ((consecutiveInterval N H).erase p).prod id
    apply hp.prime.not_dvd_finsetProd
    intro k hk hpk
    have hkMem : k ∈ consecutiveInterval N H := Finset.mem_of_mem_erase hk
    have hkPos : 0 < k :=
      lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hkMem).1
    have hkLe : k ≤ N + H := (Finset.mem_Ioc.mp hkMem).2
    have hkLt : k < 2 * p := hkLe.trans_lt hsumLt
    have hkp : k = p := by
      rcases hpk with ⟨c, rfl⟩
      have hcPos : 0 < c := by
        by_contra hc
        have : c = 0 := Nat.eq_zero_of_not_pos hc
        subst c
        simp at hkPos
      have hcLt : c < 2 := by
        apply (Nat.mul_lt_mul_left hp.pos).mp
        simpa [mul_comm] using hkLt
      have hc : c = 1 := by omega
      simp [hc]
    exact (Finset.ne_of_mem_erase hk) hkp
  constructor
  · rw [hproduct]
    exact dvd_mul_right p remainder
  · rw [hproduct, pow_two]
    intro hdvd
    exact hpNotDvdRemainder
      ((Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd)

/-- The elementary first conclusion of Tao's Lemma 3.1 (`hvin`) for positive
starting points. The source's unrestricted natural-number wording has the
exceptional interval `{1}` at `N = 0`, since the literal definition makes
`1` powerful. -/
theorem IsVeryBadInterval.length_lt_start_of_pos {N H : ℕ}
    (hN : 1 ≤ N) (hveryBad : IsVeryBadInterval N H) : H < N := by
  by_contra hnot
  have hNLeH : N ≤ H := by omega
  have hsumTwo : 2 ≤ N + H := by omega
  obtain ⟨p, hp, hpLower, hpUpper⟩ := taoProposition23i hsumTwo
  have hNltp : N < p := by omega
  have hsumLt : N + H < 2 * p := by omega
  obtain ⟨hpdvd, hpSqNotDvd⟩ :=
    prime_dvd_consecutiveProduct_exactly_once hp hNltp hpUpper hsumLt
  exact hpSqNotDvd (hveryBad.2 p hp hpdvd)

end Tao2026
