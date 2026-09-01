import GafniTao.FordLemma32Finite

/-!
# Ford Lemma 3.2: source parameter shell

This file derives the finite core's product and size hypotheses from the
literal prime-set and scale hypotheses in Ford's Lemma 3.2.  The prime set is
kept explicit: Ford only uses that it has `k^3` elements, all prime, and lies
in `(M, 2*M]`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_prime_interval_card_le
    {k M : ℕ} {S : Finset ℕ}
    (hcard : S.card = k ^ 3)
    (hinterval : ∀ p ∈ S, M < p ∧ p ≤ 2 * M) :
    k ^ 3 ≤ M := by
  have hsub : S ⊆ Finset.Ioc M (2 * M) := by
    intro p hp
    exact Finset.mem_Ioc.mpr (hinterval p hp)
  calc
    k ^ 3 = S.card := hcard.symm
    _ ≤ (Finset.Ioc M (2 * M)).card := Finset.card_le_card hsub
    _ = M := by simp only [Nat.card_Ioc]; omega

theorem ford_prime_product_gt_base_power
    {M : ℕ} {S : Finset ℕ}
    (hne : S.Nonempty)
    (hlower : ∀ p ∈ S, M < p) :
    M ^ S.card < ∏ p ∈ S, p := by
  calc
    M ^ S.card < (M + 1) ^ S.card := by
      exact Nat.pow_lt_pow_left (by omega) (Finset.card_ne_zero.mpr hne)
    _ = ∏ _p ∈ S, (M + 1) := by simp
    _ ≤ ∏ p ∈ S, p := by
      exact Finset.prod_le_prod' fun p hp => (Nat.succ_le_iff.mpr (hlower p hp))

theorem ford_lemma_3_2_source_exponent_le
    {k d : ℕ} (hk2 : 2 ≤ k) (hdk : d ≤ k) :
    d + (k - d) * (k - d - 1) ≤ k ^ 2 - k := by
  have hnle : k - d ≤ k := Nat.sub_le k d
  have hpredle : k - d - 1 ≤ k - 1 := Nat.sub_le_sub_right hnle 1
  have hmul := Nat.mul_le_mul_left (k - d) hpredle
  have hkpred : 1 ≤ k - 1 := by omega
  have hdmul : d ≤ d * (k - 1) := by
    simpa only [mul_one] using Nat.mul_le_mul_left d hkpred
  have hsplit : k - d + d = k := Nat.sub_add_cancel hdk
  have htarget : k ^ 2 - k = k * (k - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [htarget]
  nlinarith

theorem ford_lemma_3_2_four_k_four_lt
    {k M P r : ℕ}
    (hk4 : 4 ≤ k) (hcardM : k ^ 3 ≤ M)
    (hr2 : 2 ≤ r) (hMP : M ^ r ≤ P) :
    4 * k ^ 4 < P := by
  have hMpos : 0 < M := lt_of_lt_of_le (pow_pos (by omega) 3) hcardM
  have h4k2 : 4 < k ^ 2 := by nlinarith
  have hk4pos : 0 < k ^ 4 := pow_pos (by omega) _
  have hfirst : 4 * k ^ 4 < k ^ 6 := by
    calc
      4 * k ^ 4 < k ^ 2 * k ^ 4 := (Nat.mul_lt_mul_right hk4pos).2 h4k2
      _ = k ^ 6 := by ring
  have hsquare : k ^ 6 ≤ M ^ 2 := by
    calc
      k ^ 6 = (k ^ 3) ^ 2 := by ring
      _ ≤ M ^ 2 := Nat.pow_le_pow_left hcardM 2
  have hpow : M ^ 2 ≤ M ^ r := Nat.pow_le_pow_right hMpos hr2
  exact hfirst.trans_le (hsquare.trans (hpow.trans hMP))

theorem ford_lemma_3_2_source_product
    {k d M P : ℕ} {S : Finset ℕ}
    (hk4 : 4 ≤ k) (hdk : d ≤ k)
    (hMtwo : 2 ≤ M) (hPpos : 0 < P)
    (hcard : S.card = k ^ 3)
    (hlower : ∀ p ∈ S, M < p)
    (hPM : P ≤ M ^ (k + 1)) :
    P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p := by
  have hkpos : 0 < k := by omega
  have hSne : S.Nonempty := Finset.card_pos.mp (by simpa [hcard] using pow_pos hkpos 3)
  have he : d + (k - d) * (k - d - 1) ≤ k ^ 2 - k :=
    ford_lemma_3_2_source_exponent_le (by omega) hdk
  have hpowP :
      P ^ (d + (k - d) * (k - d - 1)) ≤ P ^ (k ^ 2 - k) :=
    Nat.pow_le_pow_right hPpos he
  have hbase : P ^ (k ^ 2 - k) ≤ (M ^ (k + 1)) ^ (k ^ 2 - k) :=
    Nat.pow_le_pow_left hPM _
  have hsubsq : k ^ 2 - k + k = k ^ 2 :=
    Nat.sub_add_cancel (by nlinarith)
  have hltExp : (k + 1) * (k ^ 2 - k) < k ^ 3 := by
    nlinarith
  have htoM : (M ^ (k + 1)) ^ (k ^ 2 - k) < M ^ (k ^ 3) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) hltExp
  have hprod : M ^ S.card < ∏ p ∈ S, p :=
    ford_prime_product_gt_base_power hSne hlower
  rw [hcard] at hprod
  exact hpowP.trans_lt (hbase.trans_lt (htoM.trans hprod))

/-- Ford Lemma 3.2 at integral endpoints.  All auxiliary hypotheses of the
finite maximizing-system argument are derived here from the source scale and
prime-interval assumptions. -/
theorem ford_lemma_3_2_nat_endpoints
    {k d T P s Q q r M : ℕ} (S : Finset ℕ)
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk4 : 4 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdr : d < r) (hds : d + 1 ≤ s)
    (hM : k ≤ M) (hPM : P ≤ M ^ (k + 1)) (hMP : M ^ r ≤ P)
    (hQ : 32 * s ^ 2 * M < Q) (hQP : Q ≤ P)
    (hq : 0 < q) (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (hcard : S.card = k ^ 3)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hinterval : ∀ p ∈ S, M < p ∧ p ≤ 2 * M) :
    ∃ (Ψ : FordIntegerPolynomialSystem k d T) (p : ℕ), p ∈ S ∧
      ∃ c : ZMod p,
        fordKCount Ψ₀ s P Q q ≤
          4 * k ^ 3 * k.factorial *
            p ^ ((2 * s - d) +
              ((r - d - 1) * (r - d) / 2 + r * d)) *
            fordLCount
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P (Q / p) p q r := by
  have hdk : d ≤ k := hdr.le.trans hrk
  have hcardM : k ^ 3 ≤ M := ford_prime_interval_card_le hcard hinterval
  have hPbig : 4 * k ^ 4 < P :=
    ford_lemma_3_2_four_k_four_lt hk4 hcardM hr2 hMP
  have hMtwo : 2 ≤ M := le_trans (by omega) (hk4.trans hM)
  have hPpos : 0 < P := by
    exact lt_of_lt_of_le (pow_pos (by omega) r) hMP
  have hsource :
      P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p :=
    ford_lemma_3_2_source_product hk4 hdk hMtwo hPpos hcard
      (fun p hp => (hinterval p hp).1) hPM
  have hQrange : 0 < Q ∧ Q ≤ P := ⟨by omega, hQP⟩
  obtain ⟨Ψ, p, hpS, c, hbound⟩ := ford_lemma_3_2_finite_core
    S Ψ₀ (by omega) hdk hds (by omega) hdr hrk hPbig
      hQrange.1 hq hTpos hT hprime
      (fun p hp => lt_of_le_of_lt hM (hinterval p hp).1)
      (fun p hp => (hinterval p hp).2) hsource hQ
  refine ⟨Ψ, p, hpS, c, ?_⟩
  simpa only [hcard] using hbound

#print axioms ford_prime_interval_card_le
#print axioms ford_prime_product_gt_base_power
#print axioms ford_lemma_3_2_source_exponent_le
#print axioms ford_lemma_3_2_four_k_four_lt
#print axioms ford_lemma_3_2_source_product
#print axioms ford_lemma_3_2_nat_endpoints

end

end GafniTao
