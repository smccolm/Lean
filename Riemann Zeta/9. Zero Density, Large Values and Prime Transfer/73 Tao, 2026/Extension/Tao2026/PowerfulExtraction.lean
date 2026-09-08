import Tao2026.IntervalMultiples
import Tao2026.VeryBadIntervals

/-!
# Powerful-core extraction for Tao's Lemma 3.2

The exponent-one prime part is separated canonically from each positive
integer. In a very bad interval, its primes are at most the interval length,
while the complementary factor is powerful.
-/

namespace Tao2026

noncomputable def singleExponentFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => if e = 1 then 1 else 0) (by simp)

noncomputable def powerfulCoreFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => if e = 1 then 0 else e) (by simp)

noncomputable def singleExponentPart (n : ℕ) : ℕ :=
  (singleExponentFactorization n).prod (· ^ ·)

noncomputable def powerfulCore (n : ℕ) : ℕ :=
  (powerfulCoreFactorization n).prod (· ^ ·)

theorem singleExponentFactorization_add_powerfulCoreFactorization (n : ℕ) :
    singleExponentFactorization n + powerfulCoreFactorization n = n.factorization := by
  ext p
  simp only [singleExponentFactorization, powerfulCoreFactorization,
    Finsupp.add_apply, Finsupp.mapRange_apply]
  by_cases h : n.factorization p = 1 <;> simp [h]

theorem singleExponentFactorization_le (n : ℕ) :
    singleExponentFactorization n ≤ n.factorization := by
  intro p
  simp only [singleExponentFactorization, Finsupp.mapRange_apply]
  split_ifs <;> omega

theorem powerfulCoreFactorization_le (n : ℕ) :
    powerfulCoreFactorization n ≤ n.factorization := by
  intro p
  simp only [powerfulCoreFactorization, Finsupp.mapRange_apply]
  split_ifs <;> omega

theorem factorization_singleExponentPart (n : ℕ) :
    (singleExponentPart n).factorization = singleExponentFactorization n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (singleExponentFactorization_le n)

theorem factorization_powerfulCore (n : ℕ) :
    (powerfulCore n).factorization = powerfulCoreFactorization n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (powerfulCoreFactorization_le n)

theorem singleExponentPart_mul_powerfulCore {n : ℕ} (hn : n ≠ 0) :
    singleExponentPart n * powerfulCore n = n := by
  rw [singleExponentPart, powerfulCore,
    ← Finsupp.prod_add_index (f := singleExponentFactorization n)
      (g := powerfulCoreFactorization n)]
  · rw [singleExponentFactorization_add_powerfulCoreFactorization,
      Nat.prod_factorization_pow_eq_self hn]
  · intro p hp
    simp
  · intro p hp a b
    exact pow_add p a b

theorem singleExponentPart_pos {n : ℕ} (hn : 0 < n) :
    0 < singleExponentPart n := by
  have hproduct := singleExponentPart_mul_powerfulCore hn.ne'
  have hmul : 0 < singleExponentPart n * powerfulCore n := by
    rw [hproduct]
    exact hn
  exact pos_of_mul_pos_left hmul (Nat.zero_le _)

theorem powerfulCore_pos {n : ℕ} (hn : 0 < n) : 0 < powerfulCore n := by
  have hproduct := singleExponentPart_mul_powerfulCore hn.ne'
  have hmul : 0 < singleExponentPart n * powerfulCore n := by
    rw [hproduct]
    exact hn
  exact pos_of_mul_pos_right hmul (Nat.zero_le _)

theorem prime_dvd_singleExponentPart_iff {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) :
    p ∣ singleExponentPart n ↔ n.factorization p = 1 := by
  rw [hp.dvd_iff_one_le_factorization (singleExponentPart_pos hn).ne',
    factorization_singleExponentPart, singleExponentFactorization,
    Finsupp.mapRange_apply]
  split_ifs with h
  · simp [h]
  · constructor
    · omega
    · exact fun h' => (h h').elim

theorem squarefree_singleExponentPart {n : ℕ} (hn : 0 < n) :
    Squarefree (singleExponentPart n) := by
  rw [Nat.squarefree_iff_factorization_le_one (singleExponentPart_pos hn).ne']
  intro p
  rw [factorization_singleExponentPart]
  simp only [singleExponentFactorization, Finsupp.mapRange_apply]
  split_ifs <;> omega

theorem powerful_powerfulCore {n : ℕ} (hn : 0 < n) : Powerful (powerfulCore n) := by
  rw [powerful_iff_factorization_two_le (powerfulCore_pos hn).ne']
  intro p hp
  rw [factorization_powerfulCore]
  have hpSupport : p ∈ (powerfulCoreFactorization n).support := by
    rw [← Nat.support_factorization] at hp
    rwa [factorization_powerfulCore] at hp
  rw [Finsupp.mem_support_iff] at hpSupport
  simp only [powerfulCoreFactorization, Finsupp.mapRange_apply] at hpSupport ⊢
  by_cases hOne : n.factorization p = 1
  · simp [hOne] at hpSupport
  · simp only [if_neg hOne]
    have hZero : n.factorization p ≠ 0 := by
      intro h
      rw [h] at hpSupport
      simp at hpSupport
    omega

theorem eq_of_mem_consecutiveInterval_of_prime_dvd
    {N H p j k : ℕ} (hj : j ∈ consecutiveInterval N H)
    (hk : k ∈ consecutiveInterval N H) (hHltp : H < p)
    (hpj : p ∣ j) (hpk : p ∣ k) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hdiffPos : 0 < k - j := Nat.sub_pos_of_lt hjk
    have hdiffLe : k - j ≤ H := by
      have hjLower := (Finset.mem_Ioc.mp hj).1
      have hkUpper := (Finset.mem_Ioc.mp hk).2
      omega
    have hpDiff : p ∣ k - j := Nat.dvd_sub hpk hpj
    exact (not_lt_of_ge (Nat.le_of_dvd hdiffPos hpDiff))
      (hdiffLe.trans_lt hHltp)
  · have hdiffPos : 0 < j - k := Nat.sub_pos_of_lt hkj
    have hdiffLe : j - k ≤ H := by
      have hkLower := (Finset.mem_Ioc.mp hk).1
      have hjUpper := (Finset.mem_Ioc.mp hj).2
      omega
    have hpDiff : p ∣ j - k := Nat.dvd_sub hpj hpk
    exact (not_lt_of_ge (Nat.le_of_dvd hdiffPos hpDiff))
      (hdiffLe.trans_lt hHltp)

theorem factorization_consecutiveProduct_eq_one_of_mem_singleExponent
    {N H k p : ℕ} (hk : k ∈ consecutiveInterval N H)
    (hp : p.Prime) (hHltp : H < p)
    (hfac : k.factorization p = 1) :
    (consecutiveProduct N H).factorization p = 1 := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [consecutiveProduct, Nat.factorization_prod_apply]
  · calc
      ∑ j ∈ consecutiveInterval N H, j.factorization p =
          k.factorization p := by
        apply Finset.sum_eq_single k
        · intro j hj hjne
          have hjPos : 0 < j := by
            have := (Finset.mem_Ioc.mp hj).1
            omega
          have hnotDvd : ¬p ∣ j := by
            intro hpj
            have hpk : p ∣ k :=
              (hp.dvd_iff_one_le_factorization hkPos.ne').mpr (by omega)
            exact hjne (eq_of_mem_consecutiveInterval_of_prime_dvd
              hj hk hHltp hpj hpk)
          rw [hp.dvd_iff_one_le_factorization hjPos.ne'] at hnotDvd
          omega
        · exact fun h => (h hk).elim
      _ = 1 := hfac
  · intro j hj
    have := (Finset.mem_Ioc.mp hj).1
    omega

theorem prime_dvd_singleExponentPart_le_length_of_veryBad
    {N H k p : ℕ} (hveryBad : IsVeryBadInterval N H)
    (hk : k ∈ consecutiveInterval N H) (hp : p.Prime)
    (hpCoeff : p ∣ singleExponentPart k) : p ≤ H := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hfac : k.factorization p = 1 :=
    (prime_dvd_singleExponentPart_iff hkPos hp).mp hpCoeff
  by_contra hnot
  have hHltp : H < p := by omega
  have hproductFac := factorization_consecutiveProduct_eq_one_of_mem_singleExponent
    hk hp hHltp hfac
  have hpk : p ∣ k :=
    (hp.dvd_iff_one_le_factorization hkPos.ne').mpr (by omega)
  have hpProduct : p ∣ consecutiveProduct N H := by
    rw [consecutiveProduct]
    exact dvd_trans hpk (Finset.dvd_prod_of_mem id hk)
  have hpSqProduct : p ^ 2 ∣ consecutiveProduct N H :=
    hveryBad.2 p hp hpProduct
  have htwo : 2 ≤ (consecutiveProduct N H).factorization p :=
    (hp.pow_dvd_iff_le_factorization (consecutiveProduct_ne_zero N H)).mp hpSqProduct
  omega

theorem intervalElement_eq_smallSquarefree_mul_powerfulCore
    {N H k : ℕ} (hveryBad : IsVeryBadInterval N H)
    (hk : k ∈ consecutiveInterval N H) :
    k = singleExponentPart k * powerfulCore k ∧
      Squarefree (singleExponentPart k) ∧ Powerful (powerfulCore k) ∧
      ∀ p : ℕ, p.Prime → p ∣ singleExponentPart k → p ≤ H := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  exact ⟨(singleExponentPart_mul_powerfulCore hkPos.ne').symm,
    squarefree_singleExponentPart hkPos, powerful_powerfulCore hkPos,
    fun p hp hpCoeff =>
      prime_dvd_singleExponentPart_le_length_of_veryBad hveryBad hk hp hpCoeff⟩

theorem singleExponentPart_dvd_factorial_length_of_veryBad
    {N H k : ℕ} (hveryBad : IsVeryBadInterval N H)
    (hk : k ∈ consecutiveInterval N H) : singleExponentPart k ∣ H.factorial := by
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [← Nat.factorization_le_iff_dvd
    (singleExponentPart_pos hkPos).ne' (Nat.factorial_ne_zero H)]
  intro p
  by_cases hp : p.Prime
  · by_cases hpdvd : p ∣ singleExponentPart k
    · have hpLe : p ≤ H :=
        prime_dvd_singleExponentPart_le_length_of_veryBad
          hveryBad hk hp hpdvd
      have hpFactorial : p ∣ H.factorial := Nat.dvd_factorial hp.pos hpLe
      have hleft : (singleExponentPart k).factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree
          (squarefree_singleExponentPart hkPos) hp hpdvd
      rw [hleft]
      exact (hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero H)).mp
        hpFactorial
    · rw [hp.dvd_iff_one_le_factorization
        (singleExponentPart_pos hkPos).ne'] at hpdvd
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Exact structural relation underlying Tao's Lemma 3.2. For any two
positions in a very bad interval, the extracted coefficients divide `H!`,
their cores are powerful, and the advertised linear relation holds. The
source's stronger selection of two polynomially bounded coefficients remains
the later averaging step. -/
theorem veryBadInterval_twoPosition_powerfulRelation
    {N H h₁ h₂ : ℕ} (hveryBad : IsVeryBadInterval N H)
    (hh₁ : 1 ≤ h₁) (hh₁H : h₁ ≤ H)
    (hh₂H : h₂ ≤ H) (hh₁₂ : h₁ < h₂) :
    ∃ a b n m : ℕ,
      a ∣ H.factorial ∧ b ∣ H.factorial ∧
      Powerful n ∧ Powerful m ∧
      a * n + (h₂ - h₁) = b * m ∧
      a * n = N + h₁ ∧ b * m = N + h₂ := by
  have hk₁ : N + h₁ ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    exact ⟨by omega, Nat.add_le_add_left hh₁H N⟩
  have hk₂ : N + h₂ ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  refine ⟨singleExponentPart (N + h₁), singleExponentPart (N + h₂),
    powerfulCore (N + h₁), powerfulCore (N + h₂),
    singleExponentPart_dvd_factorial_length_of_veryBad hveryBad hk₁,
    singleExponentPart_dvd_factorial_length_of_veryBad hveryBad hk₂,
    powerful_powerfulCore (by omega), powerful_powerfulCore (by omega), ?_,
    singleExponentPart_mul_powerfulCore (by omega),
    singleExponentPart_mul_powerfulCore (by omega)⟩
  have heq₁ := singleExponentPart_mul_powerfulCore (n := N + h₁) (by omega)
  have heq₂ := singleExponentPart_mul_powerfulCore (n := N + h₂) (by omega)
  omega

end Tao2026
