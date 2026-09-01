import GafniTao.FordEquation33GoodPrime

/-!
# Ford Lemma 3.2: finite source assembly

This is the complete discrete assembly of the maximizing-system argument,
good-prime equation (3.3), and equation (3.7).  The real-parameter shell of
the published lemma is kept separate from this exact finite core.
-/

namespace GafniTao

noncomputable section

theorem ford_lemma_3_2_finite_core
    {k d T P s Q q r M : ℕ} (S : Finset ℕ)
    (Ψ₀ : FordIntegerPolynomialSystem k d T)
    (hk2 : 2 ≤ k) (hdk : d ≤ k) (hds : d + 1 ≤ s)
    (hr : 0 < r) (hdr : d < r) (hrk : r ≤ k)
    (hP : 4 * k ^ 4 < P) (hQpos : 0 < Q) (hq : 0 < q)
    (hTpos : 0 < T) (hT : T ≤ P ^ d)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hkp : ∀ p ∈ S, k < p)
    (hpM : ∀ p ∈ S, p ≤ 2 * M)
    (hsource : P ^ (d + (k - d) * (k - d - 1)) < ∏ p ∈ S, p)
    (hQ : 32 * s ^ 2 * M < Q) :
    ∃ (Ψ : FordIntegerPolynomialSystem k d T) (p : ℕ), p ∈ S ∧
      ∃ c : ZMod p,
        fordKCount Ψ₀ s P Q q ≤
          4 * S.card * k.factorial *
            p ^ ((2 * s - d) +
              ((r - d - 1) * (r - d) / 2 + r * d)) *
            fordLCount
              (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
              s P (Q / p) p q r := by
  obtain ⟨Ψ, hmax⟩ := exists_fordKMaximal s P Q q Ψ₀
  have hΨ₀ : fordKCount Ψ₀ s P Q q ≤ fordKCount Ψ s P Q q := hmax Ψ₀
  have hKD := fordK_le_two_distinct_of_maximal Ψ
    (by omega) hP hQpos hq hmax
  have hKpos : 0 < fordKCount Ψ s P Q q := by
    have hdiag := fordK_diagonal_lower Ψ s P Q q
    have hJdiag := ford_floor_pow_le_vinogradovMoment s k (P := (Q : ℝ))
    have hJpos : 0 < fordVinogradovMomentNat s k Q := by
      have hJdiag' : Q ^ s ≤ fordVinogradovMomentNat s k Q := by
        simpa [fordVinogradovMoment] using hJdiag
      exact lt_of_lt_of_le (pow_pos hQpos s) hJdiag'
    have hPpos : 0 < P := lt_trans (by positivity) hP
    exact lt_of_lt_of_le
      (mul_pos (pow_pos hPpos k) hJpos) hdiag
  have hDpos : 0 < Nat.card (FordKDistinctSolution Ψ s P Q q) := by
    omega
  obtain ⟨p, hpS, hpT, hD⟩ := ford_equation_3_3_distinct_good_prime
    S Ψ hdk hDpos hprime hsource hTpos hT
  have hp := hprime p hpS
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hS3⟩ := ford_equation_3_7_source
    (P := P) (s := s) (Q := Q) (q := q) (r := r) (M := M)
    Ψ hk2 hdk hds hq hp (hkp p hpS) hr hdr hrk hpT
      (hpM p hpS) hQ
  refine ⟨Ψ, p, hpS, c, ?_⟩
  let L : ℕ := fordLCount
    (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
    s P (Q / p) p q r
  let E : ℕ := (2 * s - d) +
    ((r - d - 1) * (r - d) / 2 + r * d)
  calc
    fordKCount Ψ₀ s P Q q ≤ fordKCount Ψ s P Q q := hΨ₀
    _ ≤ 2 * Nat.card (FordKDistinctSolution Ψ s P Q q) := hKD
    _ ≤ 2 * (S.card * fordS3Count (P := P) (p := p) Ψ hdk s Q q) :=
      Nat.mul_le_mul_left 2 hD
    _ ≤ 2 * (S.card * (2 * k.factorial * p ^ E * L)) := by
      dsimp [E, L]
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left S.card hS3)
    _ = 4 * S.card * k.factorial * p ^ E * L := by ring

#print axioms ford_lemma_3_2_finite_core

end

end GafniTao
