import Tao2026.ErdosSelfridgeSource

/-!
# Power-free coefficients in the Erdős--Selfridge setup

This file begins the proof of the source prime-multiplicity theorem.  It
formalizes equation (3) on journal page 293: every positive integer is an
`l`-th power times its canonical `l`-power-free coefficient, obtained by
reducing every prime valuation modulo `l`.
-/

namespace Tao2026

noncomputable def powerFreeFactorization (l n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e % l) (by simp)

noncomputable def powerRootFactorization (l n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e / l) (by simp)

noncomputable def powerFreePart (l n : ℕ) : ℕ :=
  (powerFreeFactorization l n).prod (· ^ ·)

noncomputable def powerRootPart (l n : ℕ) : ℕ :=
  (powerRootFactorization l n).prod (· ^ ·)

theorem powerFreeFactorization_le (l n : ℕ) :
    powerFreeFactorization l n ≤ n.factorization := by
  intro p
  simp only [powerFreeFactorization, Finsupp.mapRange_apply]
  exact Nat.mod_le _ _

theorem powerRootFactorization_le (l n : ℕ) :
    powerRootFactorization l n ≤ n.factorization := by
  intro p
  simp only [powerRootFactorization, Finsupp.mapRange_apply]
  exact Nat.div_le_self _ _

theorem factorization_powerFreePart (l n : ℕ) :
    (powerFreePart l n).factorization = powerFreeFactorization l n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (powerFreeFactorization_le l n)

theorem factorization_powerRootPart (l n : ℕ) :
    (powerRootPart l n).factorization = powerRootFactorization l n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (powerRootFactorization_le l n)

theorem powerFreePart_ne_zero (l n : ℕ) : powerFreePart l n ≠ 0 := by
  rw [powerFreePart, Finsupp.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _
    (Nat.prime_of_mem_primeFactors
      (Finsupp.support_mono (powerFreeFactorization_le l n) hp)).ne_zero

theorem powerRootPart_ne_zero (l n : ℕ) : powerRootPart l n ≠ 0 := by
  rw [powerRootPart, Finsupp.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _
    (Nat.prime_of_mem_primeFactors
      (Finsupp.support_mono (powerRootFactorization_le l n) hp)).ne_zero

/-- Canonical `l`-power-free decomposition, including the exact orientation
`n = a*x^l` used in Erdős--Selfridge equation (3). -/
theorem powerFreePart_mul_powerRootPart_pow {l n : ℕ} (hn : n ≠ 0) :
    powerFreePart l n * powerRootPart l n ^ l = n := by
  apply Nat.eq_of_factorization_eq
  · exact mul_ne_zero (powerFreePart_ne_zero l n)
      (pow_ne_zero _ (powerRootPart_ne_zero l n))
  · exact hn
  · intro p
    rw [Nat.factorization_mul (powerFreePart_ne_zero l n)
        (pow_ne_zero _ (powerRootPart_ne_zero l n)),
      Nat.factorization_pow, factorization_powerFreePart,
      factorization_powerRootPart]
    change n.factorization p % l + l * (n.factorization p / l) =
      n.factorization p
    exact Nat.mod_add_div _ _

/-- The canonical coefficient is `l`-power-free: every one of its prime
valuations is strictly below `l`. -/
theorem factorization_powerFreePart_lt {l n p : ℕ} (hl : 1 ≤ l) :
    (powerFreePart l n).factorization p < l := by
  rw [factorization_powerFreePart, powerFreeFactorization,
    Finsupp.mapRange_apply]
  exact Nat.mod_lt _ (by omega)

theorem prime_dvd_powerFreePart_lt_of_large_factorization_dvd
    {l n H p : ℕ}
    (hlarge : ∀ q : ℕ, H ≤ q → q.Prime → l ∣ n.factorization q)
    (hp : p.Prime) (hpdvd : p ∣ powerFreePart l n) : p < H := by
  by_contra hnot
  have hHp : H ≤ p := by omega
  have hpos : 1 ≤ (powerFreePart l n).factorization p :=
    (hp.dvd_iff_one_le_factorization (powerFreePart_ne_zero l n)).mp hpdvd
  rw [factorization_powerFreePart, powerFreeFactorization,
    Finsupp.mapRange_apply] at hpos
  have hzero : n.factorization p % l = 0 :=
    Nat.mod_eq_zero_of_dvd (hlarge p hHp hp)
  omega

/-- Prime uniqueness in the local interval, including the boundary `p=H`. -/
theorem eq_of_mem_consecutiveInterval_of_prime_dvd_of_length_le
    {N H p j k : ℕ} (hj : j ∈ consecutiveInterval N H)
    (hk : k ∈ consecutiveInterval N H) (hHp : H ≤ p)
    (hpj : p ∣ j) (hpk : p ∣ k) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hdiffPos : 0 < k - j := Nat.sub_pos_of_lt hjk
    have hdiffLt : k - j < H := by
      have hjLower := (Finset.mem_Ioc.mp hj).1
      have hkUpper := (Finset.mem_Ioc.mp hk).2
      omega
    have hpDiff : p ∣ k - j := Nat.dvd_sub hpk hpj
    have hpLeDiff := Nat.le_of_dvd hdiffPos hpDiff
    omega
  · have hdiffPos : 0 < j - k := Nat.sub_pos_of_lt hkj
    have hdiffLt : j - k < H := by
      have hkLower := (Finset.mem_Ioc.mp hk).1
      have hjUpper := (Finset.mem_Ioc.mp hj).2
      omega
    have hpDiff : p ∣ j - k := Nat.dvd_sub hpj hpk
    have hpLeDiff := Nat.le_of_dvd hdiffPos hpDiff
    omega

/-- A prime at least the interval length contributes all of its product
valuation through the unique interval element that it divides. -/
theorem factorization_consecutiveProduct_eq_intervalElement_of_length_le
    {N H m p : ℕ} (hm : m ∈ consecutiveInterval N H)
    (hp : p.Prime) (hHp : H ≤ p) (hpm : p ∣ m) :
    (consecutiveProduct N H).factorization p = m.factorization p := by
  have hmPos : 0 < m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  rw [consecutiveProduct, Nat.factorization_prod_apply]
  · apply Finset.sum_eq_single m
    · intro j hj hjne
      have hjPos : 0 < j := by
        have := (Finset.mem_Ioc.mp hj).1
        omega
      have hpjNot : ¬p ∣ j := by
        intro hpj
        exact hjne (eq_of_mem_consecutiveInterval_of_prime_dvd_of_length_le
          hj hm hHp hpj hpm)
      rw [hp.dvd_iff_one_le_factorization hjPos.ne'] at hpjNot
      omega
    · exact fun h => (h hm).elim
  · intro j hj
    have := (Finset.mem_Ioc.mp hj).1
    omega

/-- The local negation of the source Theorem 2 conclusion. -/
def ErdosSelfridgePrimeMultiplicityFailureAt (N H l : ℕ) : Prop :=
  ∀ p : ℕ, H ≤ p → p.Prime →
    l ∣ (consecutiveProduct N H).factorization p

/-- A complete counterexample package to the source Theorem 2 statement. -/
def ErdosSelfridgePrimeMultiplicityCounterexample : Prop :=
  ∃ N H l : ℕ, 3 ≤ H ∧ 2 ≤ l ∧
    erdosSelfridgeNextPrime H ≤ N + H ∧
      ErdosSelfridgePrimeMultiplicityFailureAt N H l

theorem not_erdosSelfridgePrimeMultiplicityConclusion_iff_counterexample :
    ¬ErdosSelfridgePrimeMultiplicityConclusion ↔
      ErdosSelfridgePrimeMultiplicityCounterexample := by
  simp only [ErdosSelfridgePrimeMultiplicityConclusion,
    ErdosSelfridgePrimeMultiplicityCounterexample,
    ErdosSelfridgePrimeMultiplicityFailureAt, not_forall, not_exists,
    not_and, not_not]
  constructor
  · rintro ⟨N, H, l, hH, hl, hendpoint, hfail⟩
    exact ⟨N, H, l, hH, hl, hendpoint, hfail⟩
  · rintro ⟨N, H, l, hH, hl, hendpoint, hfail⟩
    exact ⟨N, H, l, hH, hl, hendpoint, hfail⟩

/-- Equation (3) of Erdős--Selfridge: under failure of the prime-multiplicity
conclusion, every interval element is an `l`-th power times an `l`-power-free
coefficient supported on primes strictly below the interval length. -/
theorem exists_powerFree_smallPrime_decomposition_of_failure
    {N H l m : ℕ} (hl : 2 ≤ l)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l)
    (hm : m ∈ consecutiveInterval N H) :
    ∃ a x : ℕ,
      m = a * x ^ l ∧
      (∀ p : ℕ, p.Prime → p ∣ a → p < H) ∧
      (∀ p : ℕ, a.factorization p < l) := by
  have hm0 : m ≠ 0 := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  refine ⟨powerFreePart l m, powerRootPart l m,
    (powerFreePart_mul_powerRootPart_pow hm0).symm, ?_, ?_⟩
  · intro p hp hpdvd
    apply prime_dvd_powerFreePart_lt_of_large_factorization_dvd ?_ hp hpdvd
    intro q hHq hq
    by_cases hqm : q ∣ m
    · rw [← factorization_consecutiveProduct_eq_intervalElement_of_length_le
        hm hq hHq hqm]
      exact hfail q hHq hq
    · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
      exact dvd_zero l
  · intro p
    exact factorization_powerFreePart_lt (by omega)

/-- Equation (3) simultaneously for every factor in a source counterexample. -/
theorem counterexample_forall_exists_powerFree_smallPrime_decomposition
    (hcounter : ErdosSelfridgePrimeMultiplicityCounterexample) :
    ∃ N H l : ℕ, 3 ≤ H ∧ 2 ≤ l ∧
      erdosSelfridgeNextPrime H ≤ N + H ∧
      ∀ m ∈ consecutiveInterval N H,
        ∃ a x : ℕ,
          m = a * x ^ l ∧
          (∀ p : ℕ, p.Prime → p ∣ a → p < H) ∧
          (∀ p : ℕ, a.factorization p < l) := by
  obtain ⟨N, H, l, hH, hl, hendpoint, hfail⟩ := hcounter
  refine ⟨N, H, l, hH, hl, hendpoint, ?_⟩
  intro m hm
  exact exists_powerFree_smallPrime_decomposition_of_failure hl hfail hm

end Tao2026
