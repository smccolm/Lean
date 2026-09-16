import Tao2026.SylvesterSchurExplicitTail

/-!
# Prime-counted square-root envelope for Sylvester--Schur

The square-root split only has one low-prime contribution for each prime at
most `sqrt n`.  Retaining that exact cardinality replaces the earlier exponent
`sqrt n` by `π(sqrt n)`.  An elementary reduced-residue count modulo `30`
then bounds this exponent by `sqrt n / 3` from an explicit cutoff.
-/

namespace Tao2026

open scoped BigOperators

/-- Exact prime-counted square-root split.  If every supported prime above
`sqrt n` is at most `b`, the low contribution costs only
`n ^ primeCounting (sqrt n)`. -/
theorem choose_le_primeCounting_sqrt_envelope_mul_primorial_of_high_support
    {n k b : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hsupport : ∀ p : ℕ, p.Prime → n.sqrt < p → p ∣ n.choose k → p ≤ b) :
    n.choose k ≤ n ^ n.sqrt.primeCounting * primorial b := by
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
  have hlowSubset : low ⊆ n.sqrt.primesLE := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpData.1).2
    exact Nat.mem_primesLE.mpr ⟨hpData.2, hpPrime⟩
  have hlowCard : low.card ≤ n.sqrt.primeCounting := by
    simpa using Finset.card_le_card hlowSubset
  have hlow :
      (∏ p ∈ low, contribution p) ≤ n ^ n.sqrt.primeCounting := by
    calc
      (∏ p ∈ low, contribution p) ≤ ∏ _p ∈ low, n := by
        refine Finset.prod_le_prod' ?_
        intro p _hp
        exact Nat.pow_factorization_choose_le hn
      _ = n ^ low.card := by rw [Finset.prod_const]
      _ ≤ n ^ n.sqrt.primeCounting := Nat.pow_le_pow_right hn hlowCard
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
    _ ≤ n ^ n.sqrt.primeCounting * primorial b := Nat.mul_le_mul hlow hhigh

/-- Under the no-large-prime hypothesis, the exact low-prime exponent is
`π(sqrt n)` and Hanson bounds the high contribution by `3^(k+1)`. -/
theorem choose_le_primeCounting_sqrt_envelope_mul_three_pow_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k) :
    n.choose k ≤ n ^ n.sqrt.primeCounting * 3 ^ (k + 1) := by
  have hprimorial :
      n.choose k ≤ n ^ n.sqrt.primeCounting * primorial k := by
    apply choose_le_primeCounting_sqrt_envelope_mul_primorial_of_high_support
      hn hk
    intro p hpPrime _hpSqrt hpDvd
    by_contra hpNotLe
    exact hno p hpPrime (Nat.lt_of_not_ge hpNotLe) hpDvd
  exact hprimorial.trans
    (Nat.mul_le_mul_left (n ^ n.sqrt.primeCounting)
      (primorial_le_three_pow_succ k))

/-- A numerical gap against the prime-counted envelope forces a prime above
the lower binomial index. -/
theorem exists_large_prime_dvd_choose_of_primeCounting_sqrt_three_gap
    {n k : ℕ} (hk : 4 ≤ k) (hhalf : 2 * k ≤ n)
    (hgap : k * (n ^ n.sqrt.primeCounting * 3 ^ (k + 1)) < 4 ^ k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  by_contra hnone
  have hno : ∀ p : ℕ, p.Prime → k < p → ¬p ∣ n.choose k := by
    intro p hp hkp hpdvd
    exact hnone ⟨p, hp, hkp, hpdvd⟩
  have hn : 0 < n := by omega
  have hkN : k ≤ n := by omega
  have hupper :=
    choose_le_primeCounting_sqrt_envelope_mul_three_pow_of_no_large_prime
      hn hkN hno
  have hlower : 4 ^ k < k * n.choose k :=
    four_pow_lt_mul_choose_of_two_mul_le hk hhalf
  have hupperMul :
      k * n.choose k ≤
        k * (n ^ n.sqrt.primeCounting * 3 ^ (k + 1)) :=
    Nat.mul_le_mul_left k hupper
  exact (not_lt_of_ge (hlower.trans_le hupperMul).le) hgap

/-- Consecutive-product form of the prime-counted numerical gap. -/
theorem exists_large_prime_dvd_consecutiveProduct_of_primeCounting_sqrt_three_gap
    {N H : ℕ} (hH : 4 ≤ H) (hHN : H < N)
    (hgap : H * ((N + H) ^ (N + H).sqrt.primeCounting *
      3 ^ (H + 1)) < 4 ^ H) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨p, hpPrime, hHltp, hpChoose⟩ :=
    exists_large_prime_dvd_choose_of_primeCounting_sqrt_three_gap
      hH (by omega) hgap
  refine ⟨p, hpPrime, hHltp, ?_⟩
  rw [consecutiveProduct_eq_ascFactorial,
    Nat.ascFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hpChoose H.factorial

/-- A reduced-residue count modulo `30` gives `π(m) ≤ m/3` from `m=150`. -/
theorem primeCounting_le_div_three_of_oneFifty_le
    {m : ℕ} (hm : 150 ≤ m) : m.primeCounting ≤ m / 3 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (show 30 ≤ m by omega)
  have hcount := Nat.primeCounting_add_le
    (a := 30) (k := 30) (by norm_num) (by norm_num) q
  have hpi : Nat.primeCounting 30 = 10 := by decide
  have hphi : Nat.totient 30 = 8 := by decide
  rw [hpi, hphi] at hcount
  omega

end Tao2026
