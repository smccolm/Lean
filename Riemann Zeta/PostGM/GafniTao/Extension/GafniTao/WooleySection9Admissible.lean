import GafniTao.WooleySection7
import GafniTao.WooleySection9Source

/-!
# The admissibility ledger entering Wooley Section 9

This file packages exactly the hypotheses needed to invoke Lemma 7.1 at one
node of the multigrade tree.  It also extracts one constant and one threshold
uniformly over the finitely many grades `1,...,k-1`; no asymptotic constant is
silently allowed to depend on the grade selected later.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Exact finite conditions needed by the Lemma-7.1 consumer at grade `r`
and scales `(a,b)`. -/
def WooleySection9Admissible
    (k r B a b nu B0 : ℕ) (tau epsilon : ℝ) : Prop :=
  1 ≤ nu ∧
  nu ≤ a ∧
  nu ≤ b ∧
  r * a ≤ (k - r + 1) * b ∧
  (k - r + 1) * b ≤ B ∧
  (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) ∧
  (∀ gammaVal : ℕ, gammaVal < nu →
    tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
      (a - (k - r) * gammaVal : ℕ)) ∧
  (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
    (nu : ℝ) ∧
  ((∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal) →
    ∀ gammaVal : ℕ, gammaVal < nu →
      B0 ≤ wooleySection7BPrimeNat k r a b gammaVal)

/-- Lemma 7.1 with a grade-specific constant, restated using the exact
Section-9 admissibility record. -/
theorem wooleySourcePolynomial_lemma_7_1_of_admissible
    {k r p B s a b nu c B0 : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C tau epsilon : ℝ)
    (hc : 1 ≤ c) (hphi : phi.Spaced p c) (hgamma : gamma.Admissible)
    (hadm : WooleySection9Admissible k r B a b nu B0 tau epsilon)
    (hbound : ∀ {B s a b nu c : ℕ}, [NeZero (p ^ B)] →
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
              (wooleySection7NextB k r b) b nu gamma) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      C * (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleyNextB k r b) b nu gamma := by
  rcases hadm with
    ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau, hEpsilonZero, hB0⟩
  simpa only [wooleySection7NextB_eq_wooleyNextB] using
    hbound (B := B) (s := s) (a := a) (b := b) (nu := nu) (c := c)
      hc hnu hnua hnub hab hMB hgammaK hPhiTau hEpsilonZero hB0
      phi hphi gamma hgamma

/-- A single source constant and a single lower threshold work for every
grade in `1,...,k-1`.  The proof takes finite sums of the individual positive
constants and thresholds returned by Lemma 7.1. -/
theorem wooleySourcePolynomial_lemma_7_1_uniform_grades
    {k p B s c : ℕ} [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hkp : k < p)
    (hlower : ∀ r, 1 ≤ r → r < k → WooleyPolynomialCorollary32At r p)
    (tau epsilon : ℝ) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c) (hc : 1 ≤ c)
    (gamma : WooleySourceSequence) (hgamma : gamma.Admissible) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
      ∀ {r a b nu : ℕ}, 1 ≤ r → r < k →
        WooleySection9Admissible k r B a b nu B0 tau epsilon →
        wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
          C * (p : ℝ) ^ (k ^ 2 * nu) *
            wooleySourcePolynomialMixedMean phi s r p B
              (wooleyNextB k r b) b nu gamma := by
  let I := {r : ℕ // r ∈ wooleyGradeRange (k - 1)}
  letI : Fintype I := Fintype.ofFinset
    (wooleyGradeRange (k - 1)) (by intro i; rfl)
  have hex : ∀ i : I,
      ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
        ∀ {B s a b nu c : ℕ}, [NeZero (p ^ B)] →
          1 ≤ c → 1 ≤ nu → nu ≤ a → nu ≤ b →
          i.1 * a ≤ (k - i.1 + 1) * b →
          (k - i.1 + 1) * b ≤ B →
          (∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a) →
          (∀ gammaVal : ℕ, gammaVal < nu →
            tau * (wooleySection7BPrimeNat k i.1 a b gammaVal : ℝ) ≤
              (a - (k - i.1) * gammaVal : ℕ)) →
          (wooleySection7BPrimeNat k i.1 a b 0 : ℝ) * epsilon ^ 2 <
            (nu : ℝ) →
          ((∀ gammaVal : ℕ, gammaVal < nu →
              (nu : ℤ) < wooleySection7BPrimeInt k i.1 a b gammaVal) →
            ∀ gammaVal : ℕ, gammaVal < nu →
              B0 ≤ wooleySection7BPrimeNat k i.1 a b gammaVal) →
          ∀ (phi : WooleyPolynomialSystem k), phi.Spaced p c →
          ∀ (gamma : WooleySourceSequence), gamma.Admissible →
            wooleySourcePolynomialMixedMean phi s i.1 p B a b nu gamma ≤
              C * (p : ℝ) ^ (k ^ 2 * nu) *
                wooleySourcePolynomialMixedMean phi s i.1 p B
                  (wooleySection7NextB k i.1 b) b nu gamma := by
    intro i
    let r : ℕ := i.1
    have hrange : r ∈ wooleyGradeRange (k - 1) := i.2
    have hrBounds : 1 ≤ r ∧ r ≤ k - 1 := by
      simpa only [wooleyGradeRange, mem_Icc] using hrange
    exact wooleySourcePolynomial_lemma_7_1 hpPrime hrBounds.1 (by omega)
      hkp (hlower r hrBounds.1 (by omega)) tau epsilon htau hepsilon
  choose Cr hCr B0r hbound using hex
  let C : ℝ := ∑ i : I, Cr i
  let B0 : ℕ := ∑ i : I, B0r i
  have hkTwoCases : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
  rcases hkTwoCases with hk0 | hk1 | hk
  · subst k
    exact ⟨1, le_rfl, 0, by omega⟩
  · subst k
    exact ⟨1, le_rfl, 0, by omega⟩
  · have hgrades : Nonempty I := by
      obtain ⟨r0, hr0⟩ := wooleyGradeRange_nonempty (r := k - 1) (by omega)
      exact ⟨⟨r0, hr0⟩⟩
    have hCOne : 1 ≤ C := by
      let i0 : I := Classical.choice hgrades
      have hterm : Cr i0 ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum
          (fun i _ => (hCr i).trans' (by norm_num)) (Finset.mem_univ i0)
      exact (hCr i0).trans hterm
    refine ⟨C, hCOne, B0, ?_⟩
    intro r a b nu hr hrk hadm
    have hrange : r ∈ wooleyGradeRange (k - 1) := by
      simp only [wooleyGradeRange, mem_Icc]
      omega
    let i : I := ⟨r, hrange⟩
    have hCrC : Cr i ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum
        (fun j _ => (hCr j).trans' (by norm_num)) (Finset.mem_univ i)
    have hB0 : B0r i ≤ B0 := by
      dsimp [B0]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hadmR : WooleySection9Admissible
        k r B a b nu (B0r i) tau epsilon := by
      rcases hadm with
        ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau,
          hEpsilonZero, hhard⟩
      refine ⟨hnu, hnua, hnub, hab, hMB, hgammaK, hPhiTau,
        hEpsilonZero, ?_⟩
      intro hall gammaVal hgammaVal
      exact hB0.trans (hhard hall gammaVal hgammaVal)
    have hrBound := wooleySourcePolynomial_lemma_7_1_of_admissible
      (k := k) (r := r) (p := p) (B := B) (s := s) (a := a)
      (b := b) (nu := nu) (c := c) (B0 := B0r i)
      phi gamma (Cr i) tau epsilon hc hphi hgamma hadmR
        (by
          intro B' s' a' b' nu' c' instPow
          simpa only [i] using
            (@hbound i B' s' a' b' nu' c' instPow))
    have hrest : 0 ≤ (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleyNextB k r b) b nu gamma :=
      mul_nonneg (by positivity)
        (wooleySourcePolynomialMixedMean_nonneg phi s r p B
          (wooleyNextB k r b) b nu gamma)
    calc
      _ ≤ Cr i * (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma := hrBound
      _ = Cr i * ((p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma) := by ring
      _ ≤ C * ((p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma) :=
        mul_le_mul_of_nonneg_right hCrC hrest
      _ = C * (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleyNextB k r b) b nu gamma := by ring

/-- The actual Lemma-7.1 consumer for Wooley Lemma 9.1.  The stability
hypothesis is an explicit arithmetic obligation on the source hierarchy; it
is not an analytic estimate and is discharged separately from the definitions
of the mixed means. -/
theorem wooleySourcePolynomial_lemma_9_1_of_admissible_hierarchy
    {k p B H b nu c : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (Lambda tau epsilon : ℝ)
    (hpPrime : p.Prime) (hk : 2 ≤ k) (hkp : k < p)
    (hlower : ∀ r, 1 ≤ r → r < k → WooleyPolynomialCorollary32At r p)
    (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hgamma : gamma.Admissible)
    (hnuNext : ∀ r, 1 ≤ r → r < k → nu ≤ wooleyNextB k r b)
    (hnub : nu ≤ b) (hnukb : nu ≤ k * b) (hbH : b ≤ H)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hloss : epsilon * ((H - b : ℕ) : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B0 : ℕ,
      (∀ {r a : ℕ}, 2 ≤ r → r < k →
        WooleySection9Admissible k r B a b nu B0 tau epsilon →
        WooleySection9Admissible k (r - 1) B
          (wooleyNextB k r b) b nu B0 tau epsilon) →
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
  obtain ⟨C, hC, B0, hsection7⟩ :=
    wooleySourcePolynomial_lemma_7_1_uniform_grades
      (k := k) (p := p) (B := B) (s := wooleyTriangular k) (c := c)
      hpPrime hkp hlower
      tau epsilon htau hepsilon phi hphi hc gamma hgamma
  refine ⟨C, hC, B0, ?_⟩
  intro hstable
  apply wooleySourcePolynomial_lemma_9_1_of_section7
    phi gamma (fun r a =>
      WooleySection9Admissible k r B a b nu B0 tau epsilon)
    C Lambda epsilon hpPrime.two_le hk hC hnuNext hnub hnukb hbH hscale
  · intro r a hr hrk hadm
    simpa only [Real.rpow_natCast] using hsection7 hr hrk hadm
  · intro r a hr hrk hadm
    exact hstable hr hrk hadm
  · exact hupper
  · exact hloss

#print axioms wooleySourcePolynomial_lemma_7_1_of_admissible
#print axioms wooleySourcePolynomial_lemma_7_1_uniform_grades
#print axioms wooleySourcePolynomial_lemma_9_1_of_admissible_hierarchy

end

end GafniTao
