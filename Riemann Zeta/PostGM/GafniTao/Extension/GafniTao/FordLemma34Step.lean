import GafniTao.FordCountMonotone

/-!
# Ford Lemma 3.4: one exact induction step

This is the missing consumer joining Ford Lemma 3.2 to the monotonicity in
`Q` and to the inductive `L_s` bound.  It preserves the actual selected prime,
translated polynomial system, quotient endpoint, and all finite factors.
-/

namespace GafniTao

noncomputable section

def fordLemma34PrimeExponent (s d r : ℕ) : ℕ :=
  (2 * s - d) + ((r - d - 1) * (r - d) / 2 + r * d)

/-- One literal Lemma-3.4 step.  The conclusion is a real inequality only
because the following power bookkeeping is carried out with real powers;
the underlying counts and the Lemma-3.2 estimate remain exact naturals. -/
theorem ford_lemma_3_4_one_step
    {k d T P s Q q r M Qnext B : ℕ} {LBound : ℝ}
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk4 : 4 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdr : d < r) (hds : d + 1 ≤ s)
    (hM : k ≤ M) (hPM : P ≤ M ^ (k + 1)) (hMP : M ^ r ≤ P)
    (hQ : 32 * s ^ 2 * M < Q) (hQP : Q ≤ P)
    (hq : 0 < q) (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (hpacketTwo : ∀ p ∈ fordPrimeSet k M, p ≤ 2 * M)
    (hpacketBound : ∀ p ∈ fordPrimeSet k M, p ≤ B)
    (hquotient : ∀ p ∈ fordPrimeSet k M, Q / p ≤ Qnext)
    (hL : ∀ {T' : ℕ} (Φ : FordIntegerPolynomialSystem k d T')
      (p : ℕ), p ∈ fordPrimeSet k M →
      (fordLCount Φ s P Qnext p q r : ℝ) ≤ LBound)
    (hLBound : 0 ≤ LBound) :
    (fordKCount Ψ₀ s P Q q : ℝ) ≤
      ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
        (B : ℝ) ^ fordLemma34PrimeExponent s d r * LBound := by
  obtain ⟨Ψ, p, hp, c, hK⟩ :=
    ford_lemma_3_2_canonical_prime_set Ψ₀ hk4 hr2 hrk hdr hds
      hM hPM hMP hQ hQP hq hTpos hT hpacketTwo
  have hmonoNat :
      fordLCount
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P (Q / p) p q r ≤
        fordLCount
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P Qnext p q r :=
    fordLCount_mono_Q _ (hquotient p hp)
  have hmono :
      (fordLCount
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P (Q / p) p q r : ℝ) ≤
        fordLCount
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P Qnext p q r := by
    exact_mod_cast hmonoNat
  have hLselected :
      (fordLCount
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
          s P Qnext p q r : ℝ) ≤ LBound :=
    hL _ p hp
  have hpB : (p : ℝ) ≤ B := by exact_mod_cast hpacketBound p hp
  have hpNonneg : (0 : ℝ) ≤ p := by positivity
  have hBNonneg : (0 : ℝ) ≤ B := by positivity
  have hpow :
      (p : ℝ) ^ fordLemma34PrimeExponent s d r ≤
        (B : ℝ) ^ fordLemma34PrimeExponent s d r := by
    exact pow_le_pow_left₀ hpNonneg hpB _
  have hKreal :
      (fordKCount Ψ₀ s P Q q : ℝ) ≤
        ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r *
            (fordLCount
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P (Q / p) p q r : ℝ) := by
    exact_mod_cast hK
  calc
    (fordKCount Ψ₀ s P Q q : ℝ) ≤
        ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r *
            (fordLCount
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P (Q / p) p q r : ℝ) := hKreal
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ fordLemma34PrimeExponent s d r * LBound := by
      gcongr
      exact hmono.trans hLselected
    _ ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
          (B : ℝ) ^ fordLemma34PrimeExponent s d r * LBound := by
      have hcoeff : (0 : ℝ) ≤ ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hcoeff) hLBound

#print axioms ford_lemma_3_4_one_step

end

end GafniTao
