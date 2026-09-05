import GafniTao.WooleySection9Admissible

/-!
# Arithmetic hierarchy for Wooley Sections 7--10

The source repeatedly says that its fixed hierarchy of small parameters and
the sufficiently large ambient scale make the hypotheses of Lemma 7.1
available.  This file records a concrete sufficient set of inequalities and
derives the literal `WooleySection9Admissible` predicate.  In particular, the
two conditions involving the signed depth `B'` are proved from its definition;
they are not retained as opaque hypotheses.
-/

namespace GafniTao

noncomputable section

/-- The signed Section-7 depth is never larger than the ambient numerator
`(k-r+1)b`, hence (for `r>=1`) never larger than `kb`. -/
theorem wooleySection7BPrimeNat_le_k_mul
    {k r a b gammaVal : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    wooleySection7BPrimeNat k r a b gammaVal ≤ k * b := by
  unfold wooleySection7BPrimeNat wooleySection7BPrimeInt
  have hcoeff : k - r + 1 ≤ k := by omega
  have htoNat :
      (((((k - r + 1) * b : ℕ) : ℤ) - ((r * a : ℕ) : ℤ) -
          (((k - r) * gammaVal : ℕ) : ℤ)).toNat) ≤
        ((k - r + 1) * b : ℕ) := by
    rw [Int.toNat_le]
    exact_mod_cast (show
      (((k - r + 1) * b : ℕ) : ℤ) - ((r * a : ℕ) : ℤ) -
          (((k - r) * gammaVal : ℕ) : ℤ) ≤
        (((k - r + 1) * b : ℕ) : ℤ) by omega)
  exact htoNat.trans (Nat.mul_le_mul_right b hcoeff)

/-- A compact collection of scale inequalities implies every field of the
exact Section-9 admissibility record.  The margin
`tau*k*b + k*nu <= a` is deliberately stronger than the source's pointwise
condition, so it remains stable throughout the finite iteration. -/
theorem wooleySection9Admissible_of_scale_hierarchy
    {k r B a b nu B0 : ℕ} {tau epsilon : ℝ}
    (hr : 1 ≤ r) (hrk : r < k)
    (hnu : 1 ≤ nu) (hB0nu : B0 ≤ nu)
    (hnub : nu ≤ b) (hknua : k * nu ≤ a)
    (hrel : r * a ≤ (k - r + 1) * b)
    (hB : (k - r + 1) * b ≤ B)
    (htau : 0 ≤ tau)
    (hmargin : tau * ((k * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
      (a : ℝ))
    (hepsilon : ((k * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ)) :
    WooleySection9Admissible k r B a b nu B0 tau epsilon := by
  refine ⟨hnu, ?_, hnub, hrel, hB, ?_, ?_, ?_, ?_⟩
  · have hk : 1 ≤ k := by omega
    exact (Nat.le_mul_of_pos_left nu hk).trans hknua
  · intro gammaVal hgamma
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_left k hgamma.le).trans hknua
  · intro gammaVal hgamma
    have hbp := wooleySection7BPrimeNat_le_k_mul
      (k := k) (r := r) (a := a) (b := b) (gammaVal := gammaVal)
      hr hrk.le
    have htauBp :
        tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
          tau * ((k * b : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbp) htau
    have hgammaNu : k * gammaVal ≤ k * nu :=
      Nat.mul_le_mul_left k hgamma.le
    have hsub : (k - r) * gammaVal ≤ a := by
      have : (k - r) * gammaVal ≤ k * gammaVal :=
        Nat.mul_le_mul_right gammaVal (Nat.sub_le k r)
      exact this.trans (hgammaNu.trans hknua)
    have hmargin' :
        tau * ((k * b : ℕ) : ℝ) +
            (((k - r) * gammaVal : ℕ) : ℝ) ≤ (a : ℝ) := by
      have hkgamma : (((k - r) * gammaVal : ℕ) : ℝ) ≤
          ((k * nu : ℕ) : ℝ) := by
        exact_mod_cast (show (k - r) * gammaVal ≤ k * nu by
          exact (Nat.mul_le_mul_right gammaVal (Nat.sub_le k r)).trans hgammaNu)
      linarith
    have hcastSub : ((a - (k - r) * gammaVal : ℕ) : ℝ) =
        (a : ℝ) - (((k - r) * gammaVal : ℕ) : ℝ) := by
      rw [Nat.cast_sub hsub]
    have htauSub : tau * ((k * b : ℕ) : ℝ) ≤
        ((a - (k - r) * gammaVal : ℕ) : ℝ) := by
      rw [hcastSub]
      linarith
    exact htauBp.trans htauSub
  · have hbp := wooleySection7BPrimeNat_le_k_mul
      (k := k) (r := r) (a := a) (b := b) (gammaVal := 0)
      hr hrk.le
    have heps2 : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hbp) heps2) hepsilon
  · intro hall gammaVal hgamma
    have hhard := hall gammaVal hgamma
    have hcast := wooleySection7BPrimeNat_cast hhard
    have hnuBp : nu < wooleySection7BPrimeNat k r a b gammaVal := by
      exact_mod_cast (show (nu : ℤ) <
        (wooleySection7BPrimeNat k r a b gammaVal : ℤ) by
          simpa only [hcast] using hhard)
    exact hB0nu.trans hnuBp.le

/-- The strong scale hierarchy used in Section 10 makes admissibility stable
under the predecessor call inside Lemma 9.1.  This is the literal arithmetic
edge suppressed by the phrase "our hierarchy" in the paper. -/
theorem wooleySection9Admissible_predecessor
    {k r B b nu B0 : ℕ} {tau epsilon : ℝ}
    (hk : 2 ≤ k) (hr : 2 ≤ r) (hrk : r < k)
    (hnu : 1 ≤ nu) (hB0nu : B0 ≤ nu)
    (hscaleNu : 4 * k ^ 2 * nu ≤ b)
    (hscaleB : k * b ≤ B)
    (htau : 0 ≤ tau) (htauSmall : 4 * tau * (k : ℝ) ^ 2 ≤ 1)
    (hepsilon : ((k * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ)) :
    WooleySection9Admissible k (r - 1) B
      (wooleyNextB k r b) b nu B0 tau epsilon := by
  have hrOne : 1 ≤ r := by omega
  have hrPred : 1 ≤ r - 1 := by omega
  have hrPredK : r - 1 < k := by omega
  have hdivisor := wooley_nextB_ge_divisor_scale
    (k := k) (r := r) (b := b) hrOne hrk.le
  have hkpos : 0 < k := by omega
  have hknuNext : k * nu ≤ wooleyNextB k r b := by
    have hfour : 4 * k * (k * nu) ≤ k * wooleyNextB k r b := by
      calc
        4 * k * (k * nu) = 4 * k ^ 2 * nu := by ring
        _ ≤ b := hscaleNu
        _ ≤ k * wooleyNextB k r b := hdivisor
    have hsmall : k * (k * nu) ≤ 4 * k * (k * nu) := by nlinarith
    have : k * (k * nu) ≤ k * wooleyNextB k r b := hsmall.trans hfour
    exact Nat.le_of_mul_le_mul_left this hkpos
  have hrb : r ≤ b := by
    have hkSq : k ≤ k ^ 2 := by nlinarith
    have hkScale : k ^ 2 ≤ 4 * k ^ 2 * nu := by nlinarith
    exact hrk.le.trans (hkSq.trans (hkScale.trans hscaleNu))
  have hnextMul := wooley_section7_nextB_mul_upper
    (k := k) (r := r) (b := b) hrOne
  have hrelPred :
      (r - 1) * wooleyNextB k r b ≤ (k - (r - 1) + 1) * b := by
    rw [← wooleySection7NextB_eq_wooleyNextB]
    have hleft : (r - 1) * wooleySection7NextB k r b ≤
        r * wooleySection7NextB k r b :=
      Nat.mul_le_mul_right _ (by omega)
    have hright : (k - r + 1) * b + r ≤
        (k - (r - 1) + 1) * b := by
      have hcoeff : k - (r - 1) + 1 = (k - r + 1) + 1 := by omega
      calc
        (k - r + 1) * b + r ≤ (k - r + 1) * b + b :=
          Nat.add_le_add_left hrb _
        _ = (k - (r - 1) + 1) * b := by
          rw [hcoeff]
          simp only [Nat.add_mul, one_mul]
    exact hleft.trans (hnextMul.trans hright)
  have hBPred : (k - (r - 1) + 1) * b ≤ B := by
    have hcoeff : k - (r - 1) + 1 ≤ k := by omega
    exact (Nat.mul_le_mul_right b hcoeff).trans hscaleB
  have hmargin :
      tau * ((k * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
        (wooleyNextB k r b : ℝ) := by
    have hdivisorR : (b : ℝ) ≤
        (k : ℝ) * (wooleyNextB k r b : ℝ) := by
      exact_mod_cast hdivisor
    have hscaleNuR : (4 : ℝ) * (k : ℝ) ^ 2 * (nu : ℝ) ≤
        (b : ℝ) := by
      exact_mod_cast hscaleNu
    have htauTerm :
        4 * (tau * ((k * b : ℕ) : ℝ)) ≤
          (wooleyNextB k r b : ℝ) := by
      have hkb : ((k * b : ℕ) : ℝ) = (k : ℝ) * (b : ℝ) := by
        norm_num
      rw [hkb]
      nlinarith [mul_nonneg htau (sq_nonneg (k : ℝ)),
        mul_nonneg htau (show (0 : ℝ) ≤ k by positivity)]
    have hnuTerm :
        4 * ((k * nu : ℕ) : ℝ) ≤
          (wooleyNextB k r b : ℝ) := by
      exact_mod_cast (show 4 * (k * nu) ≤ wooleyNextB k r b by
        have hmul : k * (4 * (k * nu)) ≤
            k * wooleyNextB k r b := by
          calc
            k * (4 * (k * nu)) = 4 * k ^ 2 * nu := by ring
            _ ≤ b := hscaleNu
            _ ≤ k * wooleyNextB k r b := hdivisor
        exact Nat.le_of_mul_le_mul_left hmul hkpos)
    nlinarith
  have hnuScale : nu ≤ 4 * k ^ 2 * nu := by
    have hcoeff : 1 ≤ 4 * k ^ 2 := by nlinarith
    exact Nat.le_mul_of_pos_left nu hcoeff
  exact wooleySection9Admissible_of_scale_hierarchy
    hrPred hrPredK hnu hB0nu
    (hnuScale.trans hscaleNu)
    hknuNext hrelPred hBPred htau hmargin hepsilon

/-- The exact Lemma-9.1 estimate at one Section-10 node, using the globally
chosen Lemma-7.1 constant.  All successor-validity fields are derived from
the quantitative hierarchy above. -/
theorem wooleySourcePolynomial_lemma_9_1_of_scale_hierarchy
    {k p B H b nu c B0 : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda tau epsilon : ℝ)
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hC : 1 ≤ C)
    (hnu : 1 ≤ nu) (hB0nu : B0 ≤ nu)
    (hscaleNu : 4 * k ^ 2 * nu ≤ b)
    (hscaleB : k * b ≤ B) (hbH : b ≤ H)
    (htau : 0 ≤ tau) (htauSmall : 4 * tau * (k : ℝ) ^ 2 ≤ 1)
    (hepsilonSmall : ((k * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ))
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hgamma : gamma.Admissible)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hloss : epsilon * ((H - b : ℕ) : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ))
    (hsection7 : ∀ {r B' s a b' nu' c' : ℕ}, [NeZero (p ^ B')] →
      1 ≤ r → r < k →
      ∀ (phi' : WooleyPolynomialSystem k)
        (gamma' : WooleySourceSequence),
        1 ≤ c' → phi'.Spaced p c' → gamma'.Admissible →
        WooleySection9Admissible k r B' a b' nu' B0 tau epsilon →
        wooleySourcePolynomialMixedMean phi' s r p B' a b' nu' gamma' ≤
          C * (p : ℝ) ^ (k ^ 2 * nu') *
            wooleySourcePolynomialMixedMean phi' s r p B'
              (wooleyNextB k r b') b' nu' gamma') :
    ∀ {r a : ℕ}, 1 ≤ r → r < k →
      WooleySection9Admissible k r B a b nu B0 tau epsilon →
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) r a b nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            ((r + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((b : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) / (r : ℝ)) *
          wooleyMonogradeProduct k r (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j) b
                (wooleyNextB k j b) nu Lambda gamma) := by
  have hnuNext : ∀ r, 1 ≤ r → r < k →
      nu ≤ wooleyNextB k r b := by
    intro r hr hrk
    have hdiv := wooley_nextB_ge_divisor_scale
      (k := k) (r := r) (b := b) hr hrk.le
    have hkpos : 0 < k := by omega
    have hnuB : k * nu ≤ b := by
      have hkSq : k ≤ k ^ 2 := by nlinarith
      have hfirst : k * nu ≤ k ^ 2 * nu := Nat.mul_le_mul_right nu hkSq
      have hsecond : k ^ 2 * nu ≤ 4 * k ^ 2 * nu := by nlinarith
      have : k * nu ≤ 4 * k ^ 2 * nu := hfirst.trans hsecond
      exact this.trans hscaleNu
    have hmul : k * nu ≤ k * wooleyNextB k r b := hnuB.trans hdiv
    exact Nat.le_of_mul_le_mul_left hmul hkpos
  have hnub : nu ≤ b := by
    have hcoeff : 1 ≤ 4 * k ^ 2 := by nlinarith
    have : nu ≤ 4 * k ^ 2 * nu := Nat.le_mul_of_pos_left nu hcoeff
    exact this.trans hscaleNu
  have hnukb : nu ≤ k * b := hnub.trans (Nat.le_mul_of_pos_left b (by omega))
  apply wooleySourcePolynomial_lemma_9_1_of_section7
    phi gamma (fun r a =>
      WooleySection9Admissible k r B a b nu B0 tau epsilon)
      C Lambda epsilon hp hk hC hnuNext hnub hnukb hbH hscale
  · intro r a hr hrk hadm
    simpa only [Real.rpow_natCast] using
      hsection7 hr hrk phi gamma hc hphi hgamma hadm
  · intro r a hr hrk hadm
    exact wooleySection9Admissible_predecessor hk hr hrk hnu hB0nu
      hscaleNu hscaleB htau htauSmall hepsilonSmall
  · exact hupper
  · exact hloss

#print axioms wooleySection7BPrimeNat_le_k_mul
#print axioms wooleySection9Admissible_of_scale_hierarchy
#print axioms wooleySection9Admissible_predecessor
#print axioms wooleySourcePolynomial_lemma_9_1_of_scale_hierarchy

end

end GafniTao
