import Tao2026.SylvesterSchurHundred
import Tao2026.ErdosSelfridgeHanson

/-!
# A square-root factorization envelope for Sylvester--Schur

The earlier binomial envelope assigns one factor `n` to every possible prime
at most the interval length.  This file separates primes at `sqrt n`.
Prime-power contributions below the split contribute at most `n ^ sqrt n`;
above the split, the exponent in a binomial coefficient is at most one, so the
remaining contribution is bounded by a primorial.  Hanson's all-length
primorial theorem then gives a completely explicit `3`-power envelope.
-/

namespace Tao2026

open scoped BigOperators

/-- Generic square-root split: if every supported prime above `sqrt n` is at
most `b`, the high-prime contribution is bounded by `primorial b`. -/
theorem choose_le_sqrt_envelope_mul_primorial_of_high_support
    {n k b : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hsupport : ∀ p : ℕ, p.Prime → n.sqrt < p → p ∣ n.choose k → p ≤ b) :
    n.choose k ≤ n ^ n.sqrt * primorial b := by
  classical
  let primes : Finset ℕ :=
    (Finset.range (n + 1)).filter fun p => p.Prime
  let low : Finset ℕ := primes.filter fun p => p ≤ n.sqrt
  let high : Finset ℕ := primes.filter fun p => ¬p ≤ n.sqrt
  let supportedHigh : Finset ℕ := high.filter fun p => p ≤ b
  let contribution : ℕ → ℕ := fun p => p ^ (n.choose k).factorization p
  have hfactorization :
      n.choose k = ∏ p ∈ primes, contribution p := by
    symm
    calc
      ∏ p ∈ primes, contribution p =
          ∏ p ∈ Finset.range (n + 1), contribution p := by
        dsimp [primes]
        exact Finset.prod_filter_of_ne fun p _ hp => by
          by_contra hpNotPrime
          exact hp (by
            simp [contribution,
              Nat.factorization_eq_zero_of_not_prime _ hpNotPrime])
      _ = n.choose k := Nat.prod_pow_factorization_choose n k hk
  have hlowCard : low.card ≤ n.sqrt := by
    have hsubset : low ⊆ Finset.Icc 1 n.sqrt := by
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hpData.1).2
      exact Finset.mem_Icc.mpr ⟨hpPrime.one_lt.le, hpData.2⟩
    have hcard := Finset.card_le_card hsubset
    rw [Nat.card_Icc] at hcard
    simpa using hcard
  have hlow :
      (∏ p ∈ low, contribution p) ≤ n ^ n.sqrt := by
    calc
      (∏ p ∈ low, contribution p) ≤ ∏ _p ∈ low, n := by
        refine Finset.prod_le_prod' ?_
        intro p _hp
        exact Nat.pow_factorization_choose_le hn
      _ = n ^ low.card := by rw [Finset.prod_const]
      _ ≤ n ^ n.sqrt := Nat.pow_le_pow_right hn hlowCard
  have hhighSupport :
      (∏ p ∈ high, contribution p) =
        ∏ p ∈ supportedHigh, contribution p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hpHigh hpOutside
    have hpNotLe : ¬p ≤ b := by
      intro hpb
      exact hpOutside (Finset.mem_filter.mpr ⟨hpHigh, hpb⟩)
    have hpPrime : p.Prime := by
      exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hpHigh).1).2
    have hpNotLow : ¬p ≤ n.sqrt := (Finset.mem_filter.mp hpHigh).2
    have hpNotDvd : ¬p ∣ n.choose k := by
      intro hpDvd
      exact hpNotLe
        (hsupport p hpPrime (Nat.lt_of_not_ge hpNotLow) hpDvd)
    have hzero : (n.choose k).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpNotDvd
    simp [contribution, hzero]
  have hhigh :
      (∏ p ∈ high, contribution p) ≤ primorial b := by
    have hterm :
        (∏ p ∈ supportedHigh, contribution p) ≤
          ∏ p ∈ supportedHigh, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have hpHigh := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime := by
        exact (Finset.mem_filter.mp
          (Finset.mem_filter.mp hpHigh).1).2
      have hpNotLow : ¬p ≤ n.sqrt := (Finset.mem_filter.mp hpHigh).2
      have hnlt : n < p ^ 2 :=
        Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hpNotLow)
      have hexponent : (n.choose k).factorization p ≤ 1 :=
        Nat.factorization_choose_le_one hnlt
      exact (Nat.pow_le_pow_right hpPrime.one_lt.le hexponent).trans_eq
        (pow_one p)
    have hsubset :
        supportedHigh ⊆
          (Finset.range (b + 1)).filter fun p => p.Prime := by
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpHigh := hpData.1
      have hpPrime : p.Prime := by
        exact (Finset.mem_filter.mp
          (Finset.mem_filter.mp hpHigh).1).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpData.2), hpPrime⟩
    have hprimorial :
        (∏ p ∈ supportedHigh, p) ≤ primorial b := by
      simpa [primorial] using
        (Finset.prod_le_prod_of_subset_of_one_le'
          (f := fun p : ℕ => p) hsubset
          (fun p hp _ =>
            ((Finset.mem_filter.mp hp).2.one_lt.le)))
    rw [hhighSupport]
    exact hterm.trans hprimorial
  calc
    n.choose k = ∏ p ∈ primes, contribution p := hfactorization
    _ = (∏ p ∈ low, contribution p) *
          ∏ p ∈ high, contribution p := by
      dsimp [low, high]
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ n ^ n.sqrt * primorial b := Nat.mul_le_mul hlow hhigh

/-- If `choose n k` has no prime divisor above `k`, splitting its
factorization at `sqrt n` gives a subexponential factor times `primorial k`. -/
theorem choose_le_sqrt_envelope_mul_primorial_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k) :
    n.choose k ≤ n ^ n.sqrt * primorial k := by
  apply choose_le_sqrt_envelope_mul_primorial_of_high_support hn hk
  intro p hpPrime _hpSqrt hpDvd
  by_contra hpNotLe
  exact hno p hpPrime (Nat.lt_of_not_ge hpNotLe) hpDvd

/-- In the central range `2k ≤ n`, a supported prime above `sqrt n` is in
fact at most `n / 3`: primes in `(n/3, k]` have zero binomial valuation. -/
theorem choose_le_sqrt_envelope_mul_primorial_third_of_no_large_prime
    {n k : ℕ} (hkFour : 4 ≤ k) (hhalf : 2 * k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k) :
    n.choose k ≤ n ^ n.sqrt * primorial (n / 3) := by
  have hn : 0 < n := by omega
  have hkN : k ≤ n := by omega
  apply choose_le_sqrt_envelope_mul_primorial_of_high_support hn hkN
  intro p hpPrime hpSqrt hpDvd
  by_contra hpNotLeThird
  have hthirdLt : n / 3 < p := Nat.lt_of_not_ge hpNotLeThird
  have hpLeK : p ≤ k := by
    by_contra hpNotLeK
    exact hno p hpPrime (Nat.lt_of_not_ge hpNotLeK) hpDvd
  have hpLeNSub : p ≤ n - k := by omega
  have hsqrtTwo : 2 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hpNeTwo : p ≠ 2 := by omega
  have hnLtThreeMul : n < 3 * p := by omega
  have hzero : (n.choose k).factorization p = 0 :=
    Nat.factorization_choose_of_lt_three_mul
      hpNeTwo hpLeK hpLeNSub hnLtThreeMul
  have hpos : 0 < (n.choose k).factorization p :=
    hpPrime.factorization_pos_of_dvd (Nat.choose_ne_zero hkN) hpDvd
  omega

/-- Hanson's theorem turns the primorial factor into an explicit power of
three. -/
theorem primorial_le_three_pow_succ (k : ℕ) :
    primorial k ≤ 3 ^ (k + 1) := by
  have h := erdosSelfridgeThreePrimorialConclusion_hanson (k + 1)
  rw [erdosSelfridgePrimeProduct_eq_primorial_sub_one (by omega)] at h
  simpa using h

theorem choose_le_sqrt_envelope_mul_three_pow_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k) :
    n.choose k ≤ n ^ n.sqrt * 3 ^ (k + 1) := by
  exact (choose_le_sqrt_envelope_mul_primorial_of_no_large_prime hn hk hno).trans
    (Nat.mul_le_mul_left (n ^ n.sqrt) (primorial_le_three_pow_succ k))

/-- The sharper central-range envelope, with the primorial cut off at `n/3`,
in explicit Hanson `3`-power form. -/
theorem choose_le_sqrt_envelope_mul_three_pow_third_of_no_large_prime
    {n k : ℕ} (hkFour : 4 ≤ k) (hhalf : 2 * k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k) :
    n.choose k ≤ n ^ n.sqrt * 3 ^ (n / 3 + 1) := by
  exact
    (choose_le_sqrt_envelope_mul_primorial_third_of_no_large_prime
      hkFour hhalf hno).trans
      (Nat.mul_le_mul_left (n ^ n.sqrt)
        (primorial_le_three_pow_succ (n / 3)))

/-- A numerical gap against the square-root/Hanson envelope forces a prime
larger than the lower binomial index. -/
theorem exists_large_prime_dvd_choose_of_sqrt_three_gap
    {n k : ℕ} (hk : 4 ≤ k) (hhalf : 2 * k ≤ n)
    (hgap : k * (n ^ n.sqrt * 3 ^ (k + 1)) < 4 ^ k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  by_contra hnone
  have hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k := by
    intro p hp hkp hpdvd
    exact hnone ⟨p, hp, hkp, hpdvd⟩
  have hn : 0 < n := by omega
  have hkN : k ≤ n := by omega
  have hupper :=
    choose_le_sqrt_envelope_mul_three_pow_of_no_large_prime hn hkN hno
  have hlower : 4 ^ k < k * n.choose k :=
    four_pow_lt_mul_choose_of_two_mul_le hk hhalf
  have hupperMul :
      k * n.choose k ≤ k * (n ^ n.sqrt * 3 ^ (k + 1)) :=
    Nat.mul_le_mul_left k hupper
  exact (not_lt_of_ge (hlower.trans_le hupperMul).le) hgap

/-- In the central range, the `n/3` support cutoff gives a stronger explicit
numerical gap forcing a prime divisor above `k`. -/
theorem exists_large_prime_dvd_choose_of_sqrt_three_third_gap
    {n k : ℕ} (hk : 4 ≤ k) (hhalf : 2 * k ≤ n)
    (hgap : k * (n ^ n.sqrt * 3 ^ (n / 3 + 1)) < 4 ^ k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  by_contra hnone
  have hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k := by
    intro p hp hkp hpdvd
    exact hnone ⟨p, hp, hkp, hpdvd⟩
  have hupper :=
    choose_le_sqrt_envelope_mul_three_pow_third_of_no_large_prime
      hk hhalf hno
  have hlower : 4 ^ k < k * n.choose k :=
    four_pow_lt_mul_choose_of_two_mul_le hk hhalf
  have hupperMul :
      k * n.choose k ≤ k * (n ^ n.sqrt * 3 ^ (n / 3 + 1)) :=
    Nat.mul_le_mul_left k hupper
  exact (not_lt_of_ge (hlower.trans_le hupperMul).le) hgap

/-- Consecutive-product form of the explicit square-root/Hanson gap. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_sqrt_three_gap
    {N H : ℕ} (hH : 4 ≤ H) (hHN : H < N)
    (hgap : H * ((N + H) ^ (N + H).sqrt * 3 ^ (H + 1)) < 4 ^ H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_sqrt_three_gap hH (by omega) hgap
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- Consecutive-product form of the sharper central `n/3` gap. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_sqrt_three_third_gap
    {N H : ℕ} (hH : 4 ≤ H) (hHN : H < N)
    (hgap :
      H * ((N + H) ^ (N + H).sqrt * 3 ^ ((N + H) / 3 + 1)) < 4 ^ H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_sqrt_three_third_gap hH (by omega) hgap
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

end Tao2026
