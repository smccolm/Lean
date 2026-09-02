import GafniTao.FordLemma34Raw

/-! # Ford Lemma 3.4: composition of the two finite induction steps -/

namespace GafniTao

noncomputable section

/-- The counting-theoretic induction step, indexed by the lower degree `d`.
This avoids any transport across the identity `(d+1)-1=d`: the input is the
equation-(3.10) invariant at `d+1` and the output is literally at `d`. -/
theorem ford_equation_3_10_backward_combinatorial
    {s k r j d : ℕ} {C delta P eta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hdj : d + 1 < j) (hjr : j ≤ r)
    (hP : 1 ≤ P) (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (hM : 1 < fordMScale P Φ (d + 2))
    (hkM : k ≤ ⌊fordMScale P Φ (d + 2)⌋₊)
    (hPM : P ≤ (fordMScale P Φ (d + 2)) ^ (k + 1))
    (hQbox : 32 * s ^ 2 * ⌈fordMScale P Φ (d + 2)⌉₊ <
      ⌊fordQScale P Φ (d + 1)⌋₊)
    (hpacketTwo : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      p ≤ 2 * ⌈fordMScale P Φ (d + 2)⌉₊)
    (hpacketBound : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      (p : ℝ) ≤ eta * fordMScale P Φ (d + 2))
    (hquotient : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      ((⌊fordQScale P Φ (d + 1)⌋₊ / p : ℕ) : ℝ) ≤
        fordQScale P Φ (d + 2))
    (hQ : 1 ≤ fordQScale P Φ (d + 1))
    (hmoment : FordVinogradovMomentBound s k C delta)
    (hIH : FordEquation310Eta s k r j C delta P eta Φ Esch (d + 1))
    (habsorb : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 1)⌋₊,
      fordLemma34RawBound s k r (d + 1) p C delta P eta
          (fordMScale P Φ (d + 2)) (fordQScale P Φ (d + 1))
          (fordQScale P Φ (d + 2)) (Esch.E (d + 1)) ≤
        Esch.E d * C * P ^ k *
          (fordQScale P Φ (d + 1)) ^ fordLambda34 s k delta) :
    FordEquation310Eta s k r j C delta P eta Φ Esch d := by
  intro T Ψ hT hTbound p hp q hq
  have hraw := ford_equation_3_10_L_raw Ψ
    (show d + 1 < r by omega) hr2 hrk (show d + 1 ≤ s by omega)
    hq (fordPrimeSet_prime hp) hT hP hQ hmoment
    (fun {T'} (Υ : FordIntegerPolynomialSystem k (d + 1) T') hTT' hT'PT =>
      ford_equation_3_10_K_bound Φ Esch Υ hk hr2 hrk hks hdj hjr
        hP hPbig hM hkM hPM hQbox hpacketTwo hpacketBound hquotient
        (Nat.mul_pos (fordPrimeSet_prime hp).pos hq)
        (hT.trans_le hTT') (by
          calc
            T' ≤ ⌊P⌋₊ * T := hT'PT
            _ ≤ ⌊P⌋₊ * ⌊P⌋₊ ^ d := Nat.mul_le_mul_left _ hTbound
            _ = ⌊P⌋₊ ^ (d + 1) := by rw [← pow_succ']) hmoment hIH)
  exact hraw.trans (habsorb p hp)

#print axioms ford_equation_3_10_backward_combinatorial

end

end GafniTao
