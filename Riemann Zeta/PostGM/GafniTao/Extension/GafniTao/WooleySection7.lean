import GafniTao.WooleySection7Hard
import GafniTao.WooleySourceSections68

/-!
# Wooley Lemma 7.1

The theorem below makes the source's implied constant and eventual lower
threshold explicit and uniform before the Section 7 scales are chosen.  It
then separates the literal `B' ≤ nu` and `B' > nu` alternatives and invokes
the proved easy and hard consumers respectively.
-/

namespace GafniTao

noncomputable section

theorem wooleySourcePolynomial_lemma_7_1
    {k r p : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hr : 1 ≤ r) (hrk : r < k) (hkp : k < p)
    (hlower : WooleyPolynomialCorollary32At r p)
    (tau epsilon : ℝ) (htau : 0 < tau) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
      ∀ {B s a b nu c : ℕ}, [NeZero (p ^ B)] →
        1 ≤ c → 1 ≤ nu → nu ≤ a → nu ≤ b →
        r * a ≤ (k - r + 1) * b → (k - r + 1) * b ≤ B →
        (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) →
        (∀ gammaVal : ℕ, gammaVal < nu →
          tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
            (a - (k - r) * gammaVal : ℕ)) →
        (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
          (nu : ℝ) →
        ((∀ gammaVal : ℕ, gammaVal < nu →
            (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal) →
          ∀ gammaVal : ℕ, gammaVal < nu →
            B0 ≤ wooleySection7BPrimeNat k r a b gammaVal) →
        ∀ (phi : WooleyPolynomialSystem k), phi.Spaced p c →
        ∀ (gamma : WooleySourceSequence), gamma.Admissible →
          wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
            C * (p : ℝ) ^ (k ^ 2 * nu) *
              wooleySourcePolynomialMixedMean phi s r p B
                (wooleySection7NextB k r b) b nu gamma := by
  obtain ⟨C0, hC0, B0, hcor⟩ :=
    hlower tau (epsilon ^ 2) htau (sq_pos_of_pos hepsilon)
  let C := max 1 C0
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C, hC, B0, ?_⟩
  intro B s a b nu c instPow hc hnu hnua hnub hab hMB hgammaK
    hPhiTau hEpsilonZero hB0Hard phi hphi gamma hgamma
  have haNext : a ≤ wooleySection7NextB k r b := by
    have hcover := wooley_nextB_lower (k := k) (r := r) (b := b) hr
    rw [← wooleySection7NextB_eq_wooleyNextB] at hcover
    have hmul : r * a ≤ r * wooleySection7NextB k r b := hab.trans hcover
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  by_cases heasy : ∃ gammaVal : ℕ, gammaVal < nu ∧
      wooleySection7BPrimeInt k r a b gammaVal ≤ (nu : ℤ)
  · obtain ⟨gammaVal, hgammaVal, hBPrimeEasy⟩ := heasy
    have heasyBound := wooleySourcePolynomial_section7_easy phi p nu a b B s r
      gammaVal hpPrime.two_le hr hrk hnu hnua hnub haNext hgammaVal
      hBPrimeEasy gamma
    have hCOne : (1 : ℝ) ≤ C := le_max_left _ _
    have hnonneg : 0 ≤ (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleySection7NextB k r b) b nu gamma :=
      mul_nonneg (by positivity)
        (wooleySourcePolynomialMixedMean_nonneg phi s r p B
          (wooleySection7NextB k r b) b nu gamma)
    calc
      wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma := heasyBound
      _ = 1 * ((p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma) := by ring
      _ ≤ C * ((p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma) :=
        mul_le_mul_of_nonneg_right hCOne hnonneg
      _ = C * (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma := by ring
  · have hhard : ∀ gammaVal : ℕ, gammaVal < nu →
        (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal := by
      intro gammaVal hgammaVal
      have hnot : ¬wooleySection7BPrimeInt k r a b gammaVal ≤ (nu : ℤ) :=
        fun hle => heasy ⟨gammaVal, hgammaVal, hle⟩
      omega
    have hhardBound := wooleySourcePolynomial_section7_hard_of_lower_bound
      (k := k) (r := r) (p := p) (B := B) (s := s)
      (a := a) (b := b) (nu := nu) (c := c)
      hpPrime hc hr hrk hkp hnu hnua hMB hgammaK hhard phi hphi gamma
      hgamma tau epsilon C0 hC0 B0 hcor hPhiTau hEpsilonZero
      (hB0Hard hhard)
    have hC0C : C0 ≤ C := le_max_right _ _
    have hnonneg : 0 ≤ (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleySection7NextB k r b) b nu gamma :=
      mul_nonneg (by positivity)
        (wooleySourcePolynomialMixedMean_nonneg phi s r p B
          (wooleySection7NextB k r b) b nu gamma)
    calc
      wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          C0 * (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma := hhardBound
      _ = C0 * ((p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma) := by ring
      _ ≤ C * ((p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma) :=
        mul_le_mul_of_nonneg_right hC0C hnonneg
      _ = C * (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleySection7NextB k r b) b nu gamma := by ring

#print axioms wooleySourcePolynomial_lemma_7_1

end

end GafniTao
