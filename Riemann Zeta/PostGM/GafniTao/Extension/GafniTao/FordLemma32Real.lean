import GafniTao.FordRealCounts

/-!
# Ford Lemma 3.2 at real scale endpoints

Ford's Lemma 3.4 uses real powers for `P`, `M`, and `Q`, although the
variables counted by Lemma 3.2 are integral.  Flooring `M` in both source
scale inequalities is not sound at equality endpoints, and ceiling it in
both is not sound either.  This file instead calls the finite core with
`floor P`, `floor Q`, and the harmless upper-box parameter `ceil M`, while
proving the determinant-product inequality directly from the real scale
`M` and the strict lower endpoint of the canonical prime packet.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordPrimeSet_gt_real
    {k : ℕ} {M : ℝ} {p : ℕ}
    (hp : p ∈ fordPrimeSet k ⌊M⌋₊) :
    M < p := by
  have hpFloor : ⌊M⌋₊ < p := fordPrimeSet_gt hp
  have hMlt : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  exact hMlt.trans_le (by exact_mod_cast hpFloor)

theorem ford_real_prime_product_gt_scale_power
    {M : ℝ} {S : Finset ℕ}
    (hM : 0 < M) (hne : S.Nonempty)
    (hlower : ∀ p ∈ S, M < p) :
    M ^ S.card < ((∏ p ∈ S, p : ℕ) : ℝ) := by
  calc
    M ^ S.card = ∏ _p ∈ S, M := by simp
    _ < ∏ p ∈ S, (p : ℝ) := by
      exact Finset.prod_lt_prod_of_nonempty
        (fun _ _ => hM) (fun p hp => hlower p hp) hne
    _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by
      simp only [Nat.cast_prod]

theorem ford_lemma_3_2_real_source_product
    {k d : ℕ} {M P : ℝ} {S : Finset ℕ}
    (hk4 : 4 ≤ k) (hdk : d ≤ k)
    (hM : 1 < M) (hP : 0 < P)
    (hcard : S.card = k ^ 3)
    (hlower : ∀ p ∈ S, M < p)
    (hPM : P ≤ M ^ (k + 1)) :
    ⌊P⌋₊ ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p := by
  let e : ℕ := d + (k - d) * (k - d - 1)
  have hkpos : 0 < k := by omega
  have hSne : S.Nonempty := Finset.card_pos.mp (by
    simpa [hcard] using pow_pos hkpos 3)
  have he : e ≤ k ^ 2 - k := by
    exact ford_lemma_3_2_source_exponent_le (by omega) hdk
  have hExp : (k + 1) * e < k ^ 3 := by
    have hsubsq : k ^ 2 - k + k = k ^ 2 :=
      Nat.sub_add_cancel (by nlinarith)
    have hbase : (k + 1) * (k ^ 2 - k) < k ^ 3 := by nlinarith
    exact (Nat.mul_le_mul_left (k + 1) he).trans_lt hbase
  have hfloor : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP.le
  have hfloorPow : (⌊P⌋₊ : ℝ) ^ e ≤ P ^ e :=
    pow_le_pow_left₀ (by positivity) hfloor e
  have hPpow : P ^ e ≤ (M ^ (k + 1)) ^ e :=
    pow_le_pow_left₀ (by positivity) hPM e
  have hMpow : (M ^ (k + 1)) ^ e < M ^ (k ^ 3) := by
    rw [← pow_mul]
    exact pow_lt_pow_right₀ hM hExp
  have hprod := ford_real_prime_product_gt_scale_power
    (show 0 < M by exact zero_lt_one.trans hM) hSne hlower
  rw [hcard] at hprod
  have hreal :
      ((⌊P⌋₊ ^ e : ℕ) : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact hfloorPow.trans_lt (hPpow.trans_lt (hMpow.trans hprod))
  exact_mod_cast hreal

/-- The exact finite Lemma 3.2 core exposed at Ford's real scale endpoints.
The two rounded inequalities are deliberately visible: subsequent source
scale lemmas derive them from equation (3.9), with its large strict margin.
-/
theorem ford_lemma_3_2_real_endpoints
    {k d T s q r : ℕ} {P Q M : ℝ}
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk4 : 4 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdr : d < r) (hds : d + 1 ≤ s)
    (hM : 1 < M) (hP : 0 < P)
    (hMk : k ≤ ⌊M⌋₊)
    (hPM : P ≤ M ^ (k + 1))
    (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (hQbox : 32 * s ^ 2 * ⌈M⌉₊ < ⌊Q⌋₊)
    (hq : 0 < q) (hTpos : 0 < T) (hT : T ≤ ⌊P⌋₊ ^ d)
    (hpacket : ∀ p ∈ fordPrimeSet k ⌊M⌋₊, p ≤ 2 * ⌈M⌉₊) :
    ∃ (Ψ : FordIntegerPolynomialSystem k d T) (p : ℕ),
      p ∈ fordPrimeSet k ⌊M⌋₊ ∧
      ∃ c : ZMod p,
        fordKCountReal Ψ₀ s P Q q ≤
          4 * k ^ 3 * k.factorial *
            p ^ ((2 * s - d) +
              ((r - d - 1) * (r - d) / 2 + r * d)) *
            fordLCountReal
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P ((⌊Q⌋₊ / p : ℕ) : ℝ) p q r := by
  let S := fordPrimeSet k ⌊M⌋₊
  have hdk : d ≤ k := hdr.le.trans hrk
  have hsource :
      ⌊P⌋₊ ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p := by
    apply ford_lemma_3_2_real_source_product hk4 hdk hM hP
      (fordPrimeSet_card k ⌊M⌋₊)
    · intro p hp
      exact fordPrimeSet_gt_real hp
    · exact hPM
  obtain ⟨Ψ, p, hpS, c, hbound⟩ := ford_lemma_3_2_finite_core
    S Ψ₀ (by omega) hdk hds (by omega) hdr hrk hPbig
      (by omega) hq hTpos hT
      (fun p hp => fordPrimeSet_prime hp)
      (fun p hp => lt_of_le_of_lt hMk (fordPrimeSet_gt hp))
      hpacket hsource hQbox
  refine ⟨Ψ, p, hpS, c, ?_⟩
  simpa [fordKCountReal, fordLCountReal, S, fordPrimeSet_card] using hbound

#print axioms fordPrimeSet_gt_real
#print axioms ford_real_prime_product_gt_scale_power
#print axioms ford_lemma_3_2_real_source_product
#print axioms ford_lemma_3_2_real_endpoints

end

end GafniTao
