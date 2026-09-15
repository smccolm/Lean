import Tao2026.BadIntervals

/-!
# Reduction to normalized bad intervals

This module formalizes the valid arithmetic and interval-geometric core of
Tao's Lemma 6.2.  Starting from the distinguished value `p₀² m` supplied by
Lemma 6.1, one can retain a power-of-two subinterval having that value as an
endpoint and losing less than a factor four in length.

The paper also says that the retained subinterval is "easily" admissible at
the same dyadic parameter `x`.  Literal containment does not by itself
preserve intersection with `[x / 2, x]`; the exact conclusion below therefore
records the scale-comparability bounds that do follow, rather than silently
adding that unsupported same-window assertion.
-/

namespace Tao2026

/-- The power-of-two length used in the normalized-interval reduction.  This
is the largest power of two at most `⌊(H+2)/2⌋`, equivalently the source's
largest power of two strictly below `(H+3)/2`. -/
def normalizedBadIntervalLength (H : ℕ) : ℕ :=
  2 ^ Nat.log 2 ((H + 2) / 2)

/-- Exact natural-number bounds for the normalized length.  In particular it
is non-singleton, is no longer than the parent interval, and loses less than a
factor four.  The final inequality is the integer form used to prove that one
of the two endpoint intervals fits. -/
theorem normalizedBadIntervalLength_bounds {H : ℕ} (hH : 2 ≤ H) :
    2 ≤ normalizedBadIntervalLength H ∧
      normalizedBadIntervalLength H ≤ H ∧
      H < 4 * normalizedBadIntervalLength H ∧
      2 * normalizedBadIntervalLength H < H + 3 := by
  let y := (H + 2) / 2
  have hyTwo : 2 ≤ y := by
    dsimp [y]
    omega
  have hyPos : 0 < y := by omega
  have hlo : 2 ^ Nat.log 2 y ≤ y :=
    Nat.pow_log_le_self 2 hyPos.ne'
  have hhi : y < 2 ^ (Nat.log 2 y + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) y
  have hhi' : y < 2 * 2 ^ Nat.log 2 y := by
    simpa [pow_succ, Nat.mul_comm] using hhi
  have hyLeH : y ≤ H := by
    dsimp [y]
    omega
  have hdoubleY : 2 * y ≤ H + 2 := by
    dsimp [y]
    omega
  change 2 ≤ 2 ^ Nat.log 2 y ∧
    2 ^ Nat.log 2 y ≤ H ∧
    H < 4 * 2 ^ Nat.log 2 y ∧
    2 * 2 ^ Nat.log 2 y < H + 3
  constructor
  · omega
  constructor
  · exact hlo.trans hyLeH
  constructor <;> omega

/-- One of the two intervals of normalized length having `k` as an endpoint
is contained in the parent interval. -/
theorem exists_normalized_endpoint_subinterval {N H k : ℕ} (hH : 2 ≤ H)
    (hk : k ∈ consecutiveInterval N H) :
    ∃ N' : ℕ,
      consecutiveInterval N' (normalizedBadIntervalLength H) ⊆
        consecutiveInterval N H ∧
      k ∈ consecutiveInterval N' (normalizedBadIntervalLength H) ∧
      (k = N' + 1 ∨ k = N' + normalizedBadIntervalLength H) := by
  let H' := normalizedBadIntervalLength H
  obtain ⟨hH'Two, _hH'leH, _hHfour, hfit⟩ :=
    normalizedBadIntervalLength_bounds hH
  have hkBounds : N < k ∧ k ≤ N + H := by
    simpa only [consecutiveInterval, Finset.mem_Ioc] using hk
  by_cases hleft : H' ≤ k - N
  · refine ⟨k - H', ?_, ?_, Or.inr ?_⟩
    · intro j hj
      simp only [consecutiveInterval, Finset.mem_Ioc] at hj ⊢
      omega
    · simp only [consecutiveInterval, Finset.mem_Ioc]
      omega
    · omega
  · have hright : k + H' - 1 ≤ N + H := by
      omega
    refine ⟨k - 1, ?_, ?_, Or.inl ?_⟩
    · intro j hj
      simp only [consecutiveInterval, Finset.mem_Ioc] at hj ⊢
      omega
    · simp only [consecutiveInterval, Finset.mem_Ioc]
      omega
    · omega

/-- A contained consecutive subinterval that retains the square of the
parent's largest prime is itself bad, with the same largest prime. -/
theorem isBadInterval_of_subinterval_containing_largestPrimeSquare
    {N H N' H' p k : ℕ} (hH' : 1 ≤ H')
    (hsub : consecutiveInterval N' H' ⊆ consecutiveInterval N H)
    (hk : k ∈ consecutiveInterval N' H') (hp : p.Prime)
    (hpMax : largestPrimeFactor (consecutiveProduct N H) = some p)
    (hpSqK : p ^ 2 ∣ k) :
    IsBadInterval N' H' ∧
      largestPrimeFactor (consecutiveProduct N' H') = some p := by
  have hprodDvd : consecutiveProduct N' H' ∣ consecutiveProduct N H := by
    exact Finset.prod_dvd_prod_of_subset
      (consecutiveInterval N' H') (consecutiveInterval N H) id hsub
  have hpSqChild : p ^ 2 ∣ consecutiveProduct N' H' := by
    rw [consecutiveProduct]
    exact dvd_trans hpSqK (Finset.dvd_prod_of_mem id hk)
  have hpDvdChild : p ∣ consecutiveProduct N' H' :=
    dvd_trans (dvd_pow_self p (by omega)) hpSqChild
  have hpMemChild : p ∈ (consecutiveProduct N' H').primeFactors :=
    hp.mem_primeFactors hpDvdChild (consecutiveProduct_ne_zero N' H')
  have hpMaxChild :
      largestPrimeFactor (consecutiveProduct N' H') = some p := by
    apply largestPrimeFactor_eq_some_iff.mpr
    refine ⟨hpMemChild, ?_⟩
    intro q hq
    have hqParent : q ∈ (consecutiveProduct N H).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        dvd_trans (Nat.dvd_of_mem_primeFactors hq) hprodDvd,
        consecutiveProduct_ne_zero N H⟩
    exact (largestPrimeFactor_eq_some_iff.mp hpMax).2 q hqParent
  exact ⟨⟨hH', p, hpMaxChild, hpSqChild⟩, hpMaxChild⟩

/-- A normalized bad interval retains a named largest-prime square endpoint,
its smooth cofactor, and power-of-two length. -/
def IsNormalizedBadInterval (N H p k m : ℕ) : Prop :=
  2 ≤ H ∧ IsBadInterval N H ∧ p.Prime ∧ H < p ∧
    largestPrimeFactor (consecutiveProduct N H) = some p ∧
    k ∈ consecutiveInterval N H ∧ IsSmooth m p ∧ k = p ^ 2 * m ∧
    (k = N + 1 ∨ k = N + H) ∧ ∃ r : ℕ, H = 2 ^ r

/-- Every element of a normalized bad interval is nonprime. -/
theorem IsNormalizedBadInterval.not_prime_of_mem {N H p k m j : ℕ}
    (hnorm : IsNormalizedBadInterval N H p k m)
    (hj : j ∈ consecutiveInterval N H) : ¬j.Prime :=
  hnorm.2.1.not_prime_of_mem hnorm.1 hj

/-- Every element of a normalized bad interval is smooth at its named largest
prime. -/
theorem IsNormalizedBadInterval.isSmooth_of_mem {N H p k m j : ℕ}
    (hnorm : IsNormalizedBadInterval N H p k m)
    (hj : j ∈ consecutiveInterval N H) : IsSmooth j p := by
  obtain ⟨_hH, _hbad, _hp, _hHltp, hpMax, _hk, _hm, _hkm,
    _hkEndpoint, _hpow⟩ := hnorm
  exact intervalElement_isSmooth_largestPrime hpMax hj

/-- Corrected exact form of Tao's Lemma 6.2.  Every admissible interval has a
contained normalized bad subinterval of length between `H/4` and `H`.  Its
start and endpoint remain comparable with the original dyadic parameter:
`x ≤ 4N'+1` and `N'+H' ≤ 2x`.

No same-`x` admissibility assertion is made: a subinterval around the
distinguished element need not itself meet `[x/2,x]`. -/
theorem exists_large_normalized_bad_subinterval_of_largePrime
    {x N H : ℕ}
    (hlarge : ∃ q : ℕ, q.Prime ∧ H < q ∧ q ∣ consecutiveProduct N H)
    (hadm : IsAdmissibleBadInterval x N H) :
    ∃ N' H' p k m : ℕ,
      IsNormalizedBadInterval N' H' p k m ∧
      consecutiveInterval N' H' ⊆ consecutiveInterval N H ∧
      H' ≤ H ∧ H < 4 * H' ∧
      x ≤ 4 * N' + 1 ∧ N' + H' ≤ 2 * x := by
  obtain ⟨hHleN, hNltx, hxLe, p, k, m, hp, hHltp, hpMax,
      hk, hmSmooth, hkm, _hkTwoX, _hallSmooth, _hallPrimeFree⟩ :=
    IsAdmissibleBadInterval.basic_estimates_of_largePrime hlarge hadm
  obtain ⟨hH, _hbad, _⟩ := hadm
  obtain ⟨hH'Two, hH'leH, hHfour, _hfit⟩ :=
    normalizedBadIntervalLength_bounds hH
  obtain ⟨N', hsub, hkChild, hkEndpoint⟩ :=
    exists_normalized_endpoint_subinterval hH hk
  let H' := normalizedBadIntervalLength H
  have hpSqK : p ^ 2 ∣ k := by
    rw [hkm]
    exact dvd_mul_right (p ^ 2) m
  obtain ⟨hbadChild, hpMaxChild⟩ :=
    isBadInterval_of_subinterval_containing_largestPrimeSquare
      (by omega) hsub hkChild hp hpMax hpSqK
  have hH'ltp : H' < p := hH'leH.trans_lt hHltp
  have hpow : ∃ r : ℕ, H' = 2 ^ r := by
    exact ⟨Nat.log 2 ((H + 2) / 2), rfl⟩
  have hfirst : N' + 1 ∈ consecutiveInterval N' H' := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hlast : N' + H' ∈ consecutiveInterval N' H' := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hNleN' : N ≤ N' := by
    have := hsub hfirst
    simp only [consecutiveInterval, Finset.mem_Ioc] at this
    omega
  have hendParent : N' + H' ≤ N + H := by
    have := hsub hlast
    simp only [consecutiveInterval, Finset.mem_Ioc] at this
    exact this.2
  refine ⟨N', H', p, k, m, ?_, hsub, hH'leH, hHfour, ?_, ?_⟩
  · refine ⟨hH'Two, hbadChild, hp, hH'ltp, hpMaxChild, hkChild,
      hmSmooth, hkm, hkEndpoint, hpow⟩
  · omega
  · omega

/-- Compatibility form of Lemma 6.2 from unrestricted Sylvester--Schur. -/
theorem exists_large_normalized_bad_subinterval_of_sylvesterSchur
    (hSS : SylvesterSchurConclusion) {x N H : ℕ}
    (hadm : IsAdmissibleBadInterval x N H) :
    ∃ N' H' p k m : ℕ,
      IsNormalizedBadInterval N' H' p k m ∧
      consecutiveInterval N' H' ⊆ consecutiveInterval N H ∧
      H' ≤ H ∧ H < 4 * H' ∧
      x ≤ 4 * N' + 1 ∧ N' + H' ≤ 2 * x :=
  exists_large_normalized_bad_subinterval_of_largePrime
    (hadm.exists_largePrime_of_sylvesterSchur hSS) hadm

end Tao2026
