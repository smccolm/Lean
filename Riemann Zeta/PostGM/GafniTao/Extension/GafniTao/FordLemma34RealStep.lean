import GafniTao.FordLemma34ScaleBridges

/-!
# Ford Lemma 3.4: one real-scale Lemma 3.2 step

This is the real-endpoint counterpart of the finite one-step consumer.  It
retains the selected prime, translated system, quotient endpoint, and the
literal finite count, then uses only proved monotonicity to pass to `Qnext`.
-/

namespace GafniTao

noncomputable section

theorem ford_lemma_3_4_real_one_step
    {k d T s q r : ℕ} {P Q M Qnext B LBound : ℝ}
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk4 : 4 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdr : d < r) (hds : d + 1 ≤ s)
    (hM : 1 < M) (hP : 0 < P)
    (hMk : k ≤ ⌊M⌋₊) (hPM : P ≤ M ^ (k + 1))
    (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (hQbox : 32 * s ^ 2 * ⌈M⌉₊ < ⌊Q⌋₊)
    (hq : 0 < q) (hTpos : 0 < T) (hT : T ≤ ⌊P⌋₊ ^ d)
    (hpacketTwo : ∀ p ∈ fordPrimeSet k ⌊M⌋₊, p ≤ 2 * ⌈M⌉₊)
    (hpacketBound : ∀ p ∈ fordPrimeSet k ⌊M⌋₊, (p : ℝ) ≤ B)
    (hquotient : ∀ p ∈ fordPrimeSet k ⌊M⌋₊,
      ((⌊Q⌋₊ / p : ℕ) : ℝ) ≤ Qnext)
    (hL : ∀ (Φ : FordIntegerPolynomialSystem k d T)
      (p : ℕ), p ∈ fordPrimeSet k ⌊M⌋₊ →
      (fordLCountReal Φ s P Qnext p q r : ℝ) ≤ LBound)
    (hLBound : 0 ≤ LBound) :
    (fordKCountReal Ψ₀ s P Q q : ℝ) ≤
      ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
        B ^ fordLemma34PrimeExponent s d r * LBound := by
  obtain ⟨Ψ, p, hp, c, hK⟩ :=
    ford_lemma_3_2_real_endpoints Ψ₀ hk4 hr2 hrk hdr hds hM hP hMk
      hPM hPbig hQbox hq hTpos hT hpacketTwo
  have hmonoNat := fordLCountReal_mono_Q
    (s := s) (p := p) (q := q) (r := r) (P := P)
    (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
    (hquotient p hp)
  have hmono :
      (fordLCountReal
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P ((⌊Q⌋₊ / p : ℕ) : ℝ) p q r : ℝ) ≤
        fordLCountReal
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P Qnext p q r := by
    exact_mod_cast hmonoNat
  have hLselected := hL
    (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c)) p hp
  have hpB := hpacketBound p hp
  have hpow :
      (p : ℝ) ^ fordLemma34PrimeExponent s d r ≤
        B ^ fordLemma34PrimeExponent s d r := by
    exact pow_le_pow_left₀ (by positivity) hpB _
  have hKreal :
      (fordKCountReal Ψ₀ s P Q q : ℝ) ≤
        ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r *
            (fordLCountReal
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P ((⌊Q⌋₊ / p : ℕ) : ℝ) p q r : ℝ) := by
    simpa [fordLemma34PrimeExponent] using (show
      (fordKCountReal Ψ₀ s P Q q : ℝ) ≤
        (((4 * k ^ 3 * k.factorial *
          p ^ ((2 * s - d) +
            ((r - d - 1) * (r - d) / 2 + r * d)) *
          fordLCountReal
            (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
            s P ((⌊Q⌋₊ / p : ℕ) : ℝ) p q r : ℕ) : ℝ)) by
        exact_mod_cast hK)
  calc
    (fordKCountReal Ψ₀ s P Q q : ℝ) ≤
        ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r *
            (fordLCountReal
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P ((⌊Q⌋₊ / p : ℕ) : ℝ) p q r : ℝ) := hKreal
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r * LBound := by
      gcongr
      exact hmono.trans hLselected
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          B ^ fordLemma34PrimeExponent s d r * LBound := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) hLBound

#print axioms ford_lemma_3_4_real_one_step

end

end GafniTao
