import GafniTao.WooleySection9Hierarchy
import GafniTao.WooleySection10Step
import GafniTao.WooleySection10Chain

/-!
# The actual Section 10 transition

This file discharges the admissibility and hierarchy hypotheses for both
applications of Lemma 9.1 inside a single Lemma-9.3 transition.  Its inputs
are uniform scale inequalities that will subsequently be obtained from the
one fixed Section-10 parameter hierarchy.
-/

namespace GafniTao

noncomputable section

/-- The single global loss margin controls the first Lemma-9.1 application. -/
theorem wooley_section10_first_loss_from_global
    {k r b nu : ℕ} {Lambda : ℝ}
    (hk : 2 ≤ k) (hrk : r ≤ k - 1)
    (hglobal : 2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤ (b : ℝ) * Lambda) :
    2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
      (b : ℝ) * Lambda / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by positivity
  rw [le_div_iff₀ hkR]
  have hnat : k * ((r + 1) * k ^ 2 * nu) ≤ k ^ 5 * nu := by
    have hrTop : r + 1 ≤ k := by omega
    have hfirst : (r + 1) * (k ^ 2 * nu) ≤ k * (k ^ 2 * nu) :=
      Nat.mul_le_mul_right (k ^ 2 * nu) hrTop
    calc
      k * ((r + 1) * k ^ 2 * nu) ≤ k * (k * (k ^ 2 * nu)) :=
        Nat.mul_le_mul_left k (by simpa [mul_assoc] using hfirst)
      _ = k ^ 4 * nu := by ring
      _ ≤ k ^ 5 * nu := by
        rw [show k ^ 5 * nu = (k ^ 4 * nu) * k by ring]
        exact Nat.le_mul_of_pos_right _ (by omega)
  have hcast : (k : ℝ) * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
      ((k ^ 5 * nu : ℕ) : ℝ) := by exact_mod_cast hnat
  nlinarith

/-- The same global loss margin controls every second Lemma-9.1 application,
including the worst possible one-step decrease in `b'`. -/
theorem wooley_section10_second_loss_from_global
    {k rOne b nu : ℕ} {Lambda : ℝ}
    (hk : 2 ≤ k) (hrOne : 1 ≤ rOne) (hrOneK : rOne ≤ k - 1)
    (hLambda : 0 < Lambda)
    (hglobal : 2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤ (b : ℝ) * Lambda) :
    2 * ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
      (wooleyNextB k rOne b : ℝ) * Lambda / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hdiv := wooley_nextB_ge_divisor_scale
    (k := k) (r := rOne) (b := b) hrOne (by omega)
  have hdivR : (b : ℝ) ≤
      (k : ℝ) * (wooleyNextB k rOne b : ℝ) := by
    exact_mod_cast hdiv
  rw [le_div_iff₀ hkR]
  have hnat : k ^ 2 * (((k - rOne) + 1) * k ^ 2 * nu) ≤
      k ^ 5 * nu := by
    have hcoeff : k - rOne + 1 ≤ k := by omega
    have hfirst : (k - rOne + 1) * (k ^ 2 * nu) ≤
        k * (k ^ 2 * nu) := Nat.mul_le_mul_right (k ^ 2 * nu) hcoeff
    calc
      k ^ 2 * ((k - rOne + 1) * k ^ 2 * nu) ≤
          k ^ 2 * (k * (k ^ 2 * nu)) :=
        Nat.mul_le_mul_left (k ^ 2) (by simpa [mul_assoc] using hfirst)
      _ = k ^ 5 * nu := by ring
  have hcast : (k : ℝ) ^ 2 *
        ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
      ((k ^ 5 * nu : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpre : 2 * (k : ℝ) ^ 2 *
        ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
      (b : ℝ) * Lambda := by nlinarith
  have hbnext : (b : ℝ) * Lambda ≤
      ((k : ℝ) * (wooleyNextB k rOne b : ℝ)) * Lambda :=
    mul_le_mul_of_nonneg_right hdivR hLambda.le
  have hcombined := hpre.trans hbnext
  have hcancel : (k : ℝ) *
      (2 * ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) * (k : ℝ)) ≤
      (k : ℝ) * ((wooleyNextB k rOne b : ℝ) * Lambda) := by
    calc
    (k : ℝ) *
        (2 * ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) * (k : ℝ)) =
      2 * (k : ℝ) ^ 2 *
        ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) := by ring
    _ ≤ (b : ℝ) * Lambda := hpre
    _ ≤ ((k : ℝ) * (wooleyNextB k rOne b : ℝ)) * Lambda := hbnext
    _ = (k : ℝ) *
        ((wooleyNextB k rOne b : ℝ) * Lambda) := by ring
  nlinarith

set_option maxHeartbeats 800000 in
/-- One fully discharged Section-10 transition.  It invokes the actual
Lemma-9.1 theorem twice, using the same globally selected Lemma-7.1 constant,
and then invokes the proved Lemma 9.3 consumer. -/
theorem wooleySourcePolynomial_iterationStep_of_scale_hierarchy
    {k p B H a b r nu c B0 : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda delta theta tau epsilon : ℝ)
    (hpPrime : p.Prime) (hk : 2 ≤ k)
    (hC : 1 ≤ C) (hLambda : 0 < Lambda)
    (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hdeltaTheta : 0 ≤ delta * theta)
    (hstateA : delta * theta ≤ (a : ℝ))
    (hstateB : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ))
    (hstateRel : r * a ≤ (k - r + 1) * b)
    (hnu : 1 ≤ nu) (hB0nu : B0 ≤ nu)
    (hscaleNu : 4 * k ^ 3 * nu ≤ b)
    (hscaleB : k ^ 2 * b ≤ B) (hscaleH : k * b ≤ H)
    (htau : 0 ≤ tau) (htauSmall : 4 * tau * (k : ℝ) ^ 2 ≤ 1)
    (hcurrentMargin :
      tau * ((k * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
        delta * theta)
    (hsecondMargin :
      tau * ((k ^ 2 * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
        (b : ℝ))
    (hepsilonSmall :
      ((k ^ 2 * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ))
    (hlossGlobal : epsilon * (H : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ))
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hgamma : gamma.Admissible)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hupperAll : ∀ h : ℕ, h ≤ k * b →
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ h) phi gamma ≤
        (p : ℝ) ^ (((H - h : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hsection7 : ∀ {r' B' s a' b' nu' c' : ℕ}, [NeZero (p ^ B')] →
      1 ≤ r' → r' < k →
      ∀ (phi' : WooleyPolynomialSystem k)
        (gamma' : WooleySourceSequence),
        1 ≤ c' → phi'.Spaced p c' → gamma'.Admissible →
        WooleySection9Admissible k r' B' a' b' nu' B0 tau epsilon →
        wooleySourcePolynomialMixedMean phi' s r' p B' a' b' nu' gamma' ≤
          C * (p : ℝ) ^ (k ^ 2 * nu') *
            wooleySourcePolynomialMixedMean phi' s r' p B'
              (wooleyNextB k r' b') b' nu' gamma')
    (hhierarchy :
      2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤ (b : ℝ) * Lambda) :
    WooleyIterationStep k p Lambda (C ^ ((2 * k : ℕ) : ℝ)) delta theta
      (fun r' a' b' => wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r' a' b' nu Lambda gamma) a b r := by
  have hrk' : r < k := by omega
  have hkpos : 0 < k := by omega
  have hscaleNuCurrent : 4 * k ^ 2 * nu ≤ b := by
    have hsmall : 4 * k ^ 2 * nu ≤ 4 * k ^ 3 * nu := by
      rw [show 4 * k ^ 3 * nu = (4 * k ^ 2 * nu) * k by ring]
      exact Nat.le_mul_of_pos_right _ hkpos
    exact hsmall.trans hscaleNu
  have hscaleBCurrent : k * b ≤ B := by
    have hsmall : k * b ≤ k ^ 2 * b := by
      have hkSq : k ≤ k ^ 2 := by nlinarith
      exact Nat.mul_le_mul_right b hkSq
    exact hsmall.trans hscaleB
  have hbH : b ≤ H :=
    (Nat.le_mul_of_pos_left b (by omega)).trans hscaleH
  have hepsilonCurrent : ((k * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ) := by
    have hkb : k * b ≤ k ^ 2 * b := by
      exact Nat.mul_le_mul_right b (by nlinarith)
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkb) (sq_nonneg epsilon))
      hepsilonSmall
  have hadmFirst : WooleySection9Admissible
      k r B a b nu B0 tau epsilon := by
    apply wooleySection9Admissible_of_scale_hierarchy
      hr hrk' hnu hB0nu
    · have : nu ≤ 4 * k ^ 2 * nu := by
        exact Nat.le_mul_of_pos_left nu (by nlinarith)
      exact this.trans hscaleNuCurrent
    · have hknuR : ((k * nu : ℕ) : ℝ) ≤ delta * theta := by
        have hkbR : ((k * nu : ℕ) : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast (show k * nu ≤ b by
            have : k * nu ≤ 4 * k ^ 2 * nu := by
              have hkSq : k ≤ k ^ 2 := by nlinarith
              exact (Nat.mul_le_mul_right nu hkSq).trans (by nlinarith)
            exact this.trans hscaleNuCurrent)
        nlinarith [mul_nonneg htau (show (0 : ℝ) ≤ (k * b : ℕ) by positivity)]
      exact_mod_cast (show ((k * nu : ℕ) : ℝ) ≤ (a : ℝ) by
        exact hknuR.trans hstateA)
    · exact hstateRel
    · have hcoeff : k - r + 1 ≤ k := by omega
      exact (Nat.mul_le_mul_right b hcoeff).trans hscaleBCurrent
    · exact htau
    · exact hcurrentMargin.trans hstateA
    · exact hepsilonCurrent
  have hloss (h : ℕ) : epsilon * ((H - h : ℕ) : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ) := by
    have hsub : ((H - h : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast Nat.sub_le H h
    by_cases heps : 0 ≤ epsilon
    · exact (mul_le_mul_of_nonneg_left hsub heps).trans hlossGlobal
    · have : epsilon * ((H - h : ℕ) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge heps) (by positivity)
      exact this.trans (mul_nonneg (by positivity) (by positivity))
  have h91First := wooleySourcePolynomial_lemma_9_1_of_scale_hierarchy
    phi gamma C Lambda tau epsilon hpPrime.two_le hk hC hnu hB0nu
      hscaleNuCurrent hscaleBCurrent hbH htau htauSmall hepsilonCurrent
      hphi hc hgamma hscale (hupperAll b (by
        exact Nat.le_mul_of_pos_left b (by omega))) (hloss b) hsection7
      hr hrk' hadmFirst
  have hhFirst := wooley_section10_first_loss_from_global
    hk hrk hhierarchy
  have hsecond : ∀ rOne ∈ wooleyGradeRange r,
      let bPrime := wooleyNextB k rOne b
      wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - rOne) b bPrime
            nu Lambda gamma ≤
        (C * (p : ℝ) ^ (((k ^ 2 * nu : ℕ) : ℝ))) ^
            (((k - rOne) + 1 : ℕ) : ℝ) *
          (p : ℝ) ^
            (-((bPrime : ℝ) * (1 - 1 / (k : ℝ)) * Lambda) /
              ((k - rOne : ℕ) : ℝ)) *
          wooleyMonogradeProduct k (k - rOne) (fun j =>
            wooleySourceNormalizedMixedMean
              phi p B H (wooleyTriangular k) (k - j) bPrime
                (wooleyNextB k j bPrime) nu Lambda gamma) := by
    intro rOne hrange
    dsimp only
    have hrBounds : 1 ≤ rOne ∧ rOne ≤ r := by
      simpa only [wooleyGradeRange, Finset.mem_Icc] using hrange
    have hrOneK : rOne ≤ k - 1 := hrBounds.2.trans hrk
    have hrSecond : 1 ≤ k - rOne := by omega
    have hrSecondK : k - rOne < k := by omega
    let bPrime := wooleyNextB k rOne b
    have hbPrimeUpper : bPrime ≤ k * b := by
      exact wooley_nextB_le_k_mul hrBounds.1 (by omega)
    have hdiv := wooley_nextB_ge_divisor_scale
      (k := k) (r := rOne) (b := b) hrBounds.1 (by omega)
    have hscaleNuPrime : 4 * k ^ 2 * nu ≤ bPrime := by
      have hmul : k * (4 * k ^ 2 * nu) ≤ k * bPrime := by
        calc
          k * (4 * k ^ 2 * nu) = 4 * k ^ 3 * nu := by ring
          _ ≤ b := hscaleNu
          _ ≤ k * bPrime := hdiv
      exact Nat.le_of_mul_le_mul_left hmul hkpos
    have hscaleBPrime : k * bPrime ≤ B := by
      calc
        k * bPrime ≤ k * (k * b) := Nat.mul_le_mul_left k hbPrimeUpper
        _ = k ^ 2 * b := by ring
        _ ≤ B := hscaleB
    have hbPrimeH : bPrime ≤ H :=
      hbPrimeUpper.trans hscaleH
    have hepsilonPrime : ((k * bPrime : ℕ) : ℝ) * epsilon ^ 2 <
        (nu : ℝ) := by
      have hnat : k * bPrime ≤ k ^ 2 * b := by
        calc
          k * bPrime ≤ k * (k * b) := Nat.mul_le_mul_left k hbPrimeUpper
          _ = k ^ 2 * b := by ring
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (sq_nonneg epsilon))
        hepsilonSmall
    have hknub : k * nu ≤ b := by
      have hsmall : k * nu ≤ 4 * k ^ 3 * nu := by
        have hcoeff : 1 ≤ 4 * k ^ 2 := by nlinarith
        rw [show 4 * k ^ 3 * nu = (4 * k ^ 2) * (k * nu) by ring]
        exact Nat.le_mul_of_pos_left _ hcoeff
      exact hsmall.trans hscaleNu
    have hrelSecond : (k - rOne) * b ≤
        (k - (k - rOne) + 1) * bPrime := by
      have hlower := wooley_nextB_lower
        (k := k) (r := rOne) (b := b) hrBounds.1
      have hleft : (k - rOne) * b ≤ (k - rOne + 1) * b := by
        exact Nat.mul_le_mul_right b (by omega)
      have hright : rOne * bPrime ≤ (rOne + 1) * bPrime :=
        Nat.mul_le_mul_right bPrime (by omega)
      have hcoef : k - (k - rOne) + 1 = rOne + 1 := by omega
      rw [hcoef]
      exact hleft.trans (hlower.trans hright)
    have hmarginSecond : tau * ((k * bPrime : ℕ) : ℝ) +
        ((k * nu : ℕ) : ℝ) ≤ (b : ℝ) := by
      have hnat : k * bPrime ≤ k ^ 2 * b := by
        calc
          k * bPrime ≤ k * (k * b) := Nat.mul_le_mul_left k hbPrimeUpper
          _ = k ^ 2 * b := by ring
      have hterm : tau * ((k * bPrime : ℕ) : ℝ) ≤
          tau * ((k ^ 2 * b : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hnat) htau
      linarith
    have hadmSecond : WooleySection9Admissible
        k (k - rOne) B b bPrime nu B0 tau epsilon := by
      have hnuPrime : nu ≤ bPrime := by
        have hsmall : nu ≤ 4 * k ^ 2 * nu :=
          Nat.le_mul_of_pos_left nu (by nlinarith)
        exact hsmall.trans hscaleNuPrime
      have hBSecond : (k - (k - rOne) + 1) * bPrime ≤ B := by
        have hcoeff : k - (k - rOne) + 1 ≤ k := by omega
        exact (Nat.mul_le_mul_right bPrime hcoeff).trans hscaleBPrime
      exact wooleySection9Admissible_of_scale_hierarchy
        hrSecond hrSecondK hnu hB0nu hnuPrime hknub hrelSecond
          hBSecond htau hmarginSecond hepsilonPrime
    exact wooleySourcePolynomial_lemma_9_1_of_scale_hierarchy
      phi gamma C Lambda tau epsilon hpPrime.two_le hk hC hnu hB0nu
        hscaleNuPrime hscaleBPrime hbPrimeH htau htauSmall hepsilonPrime
        hphi hc hgamma hscale (hupperAll bPrime hbPrimeUpper)
        (hloss bPrime) hsection7 hrSecond hrSecondK hadmSecond
  have hhSecond : ∀ rOne ∈ wooleyGradeRange r,
      2 * ((((k - rOne) + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (wooleyNextB k rOne b : ℝ) * Lambda / (k : ℝ) := by
    intro rOne hrange
    have hrBounds : 1 ≤ rOne ∧ rOne ≤ r := by
      simpa only [wooleyGradeRange, Finset.mem_Icc] using hrange
    exact wooley_section10_second_loss_from_global
      hk hrBounds.1 (hrBounds.2.trans hrk) hLambda hhierarchy
  exact wooleySourcePolynomial_iterationStep_of_lemma_9_1
    phi gamma C Lambda delta theta hpPrime.two_le hk hr hrk hC
      hLambda.le hdeltaTheta hstateB hhFirst h91First hhSecond hsecond

/-- Exact finite ledger required at a possible recursion node of depth `m`.
Every field is an elementary inequality in the source parameters; no mean
value estimate is packaged here. -/
def WooleySection10NodeHierarchy
    (k B H nu thetaNat m b : ℕ)
    (Lambda delta tau epsilon : ℝ) : Prop :=
  b ≤ k ^ (2 * m) * thetaNat ∧
  4 * k ^ 3 * nu ≤ b ∧
  k ^ 2 * b ≤ B ∧
  k * b ≤ H ∧
  tau * ((k * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
    delta * (thetaNat : ℝ) ∧
  tau * ((k ^ 2 * b : ℕ) : ℝ) + ((k * nu : ℕ) : ℝ) ≤
    (b : ℝ) ∧
  ((k ^ 2 * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ) ∧
  2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤ (b : ℝ) * Lambda

/-- A single finite list of inequalities at the maximal possible recursion
scale implies the node ledger at every depth below `N`. -/
theorem wooleySection10NodeHierarchy_of_global
    {k B H nu thetaNat N m b : ℕ}
    {Lambda delta tau epsilon : ℝ}
    (hk : 2 ≤ k) (hLambda : 0 < Lambda)
    (htau : 0 ≤ tau)
    (hmN : m < N) (hbUpper : b ≤ k ^ (2 * m) * thetaNat)
    (hstateB : (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) ≤ (b : ℝ))
    (hnuScale : ((4 * k ^ 3 * nu : ℕ) : ℝ) ≤
      (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)))
    (hBScale : k ^ (2 * N + 2) * thetaNat ≤ B)
    (hHScale : k ^ (2 * N + 1) * thetaNat ≤ H)
    (hcurrentMargin :
      tau * ((k * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) ≤ delta * (thetaNat : ℝ))
    (hsecondMargin :
      tau * ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) +
          ((k * nu : ℕ) : ℝ) ≤
        (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)))
    (hepsilonSmall :
      ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) *
          epsilon ^ 2 < (nu : ℝ))
    (hhierarchy : 2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤
      ((k : ℝ) ^ 2 * (delta * (thetaNat : ℝ))) * Lambda) :
    WooleySection10NodeHierarchy k B H nu thetaNat m b
      Lambda delta tau epsilon := by
  have hmle : m ≤ N := hmN.le
  have hpow : k ^ (2 * m) ≤ k ^ (2 * N) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ k) (by omega)
  have hbCap : b ≤ k ^ (2 * N) * thetaNat :=
    hbUpper.trans (Nat.mul_le_mul_right thetaNat hpow)
  have hscaleNu : 4 * k ^ 3 * nu ≤ b := by
    exact_mod_cast hnuScale.trans hstateB
  have hscaleB : k ^ 2 * b ≤ B := by
    calc
      k ^ 2 * b ≤ k ^ 2 * (k ^ (2 * N) * thetaNat) :=
        Nat.mul_le_mul_left (k ^ 2) hbCap
      _ = k ^ (2 * N + 2) * thetaNat := by
        rw [pow_add]
        ring
      _ ≤ B := hBScale
  have hscaleH : k * b ≤ H := by
    calc
      k * b ≤ k * (k ^ (2 * N) * thetaNat) :=
        Nat.mul_le_mul_left k hbCap
      _ = k ^ (2 * N + 1) * thetaNat := by
        rw [pow_succ']
        ring
      _ ≤ H := hHScale
  have hcurrent : tau * ((k * b : ℕ) : ℝ) +
      ((k * nu : ℕ) : ℝ) ≤ delta * (thetaNat : ℝ) := by
    have hnat : k * b ≤ k * (k ^ (2 * N) * thetaNat) :=
      Nat.mul_le_mul_left k hbCap
    have hnatR : ((k * b : ℕ) : ℝ) ≤
        ((k * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact (add_le_add (mul_le_mul_of_nonneg_left hnatR htau)
      (le_refl ((k * nu : ℕ) : ℝ))).trans hcurrentMargin
  have hsecond : tau * ((k ^ 2 * b : ℕ) : ℝ) +
      ((k * nu : ℕ) : ℝ) ≤ (b : ℝ) := by
    have hnat : k ^ 2 * b ≤ k ^ 2 * (k ^ (2 * N) * thetaNat) :=
      Nat.mul_le_mul_left (k ^ 2) hbCap
    have hnatR : ((k ^ 2 * b : ℕ) : ℝ) ≤
        ((k ^ 2 * (k ^ (2 * N) * thetaNat) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hterm := mul_le_mul_of_nonneg_left hnatR htau
    exact (add_le_add hterm
      (le_refl ((k * nu : ℕ) : ℝ))).trans
        (hsecondMargin.trans hstateB)
  have heps : ((k ^ 2 * b : ℕ) : ℝ) * epsilon ^ 2 < (nu : ℝ) := by
    have hnat : k ^ 2 * b ≤ k ^ 2 * (k ^ (2 * N) * thetaNat) :=
      Nat.mul_le_mul_left (k ^ 2) hbCap
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (sq_nonneg epsilon))
      hepsilonSmall
  have hh : 2 * ((k ^ 5 * nu : ℕ) : ℝ) ≤ (b : ℝ) * Lambda := by
    exact hhierarchy.trans
      (mul_le_mul_of_nonneg_right hstateB hLambda.le)
  exact ⟨hbUpper, hscaleNu, hscaleB, hscaleH, hcurrent, hsecond, heps, hh⟩

set_option maxHeartbeats 800000 in
/-- Given the one fixed hierarchy ledger at every bounded node, the actual
Lemma-9.3 transition constructs the full finite chain starting at
`(theta,theta,1)`. -/
theorem wooleySourcePolynomial_iterationChain_of_hierarchy_ledger
    {k p B H nu thetaNat c B0 N : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (C Lambda delta tau epsilon : ℝ)
    (hpPrime : p.Prime) (hk : 2 ≤ k)
    (hC : 1 ≤ C) (hLambda : 0 < Lambda)
    (htheta : 0 < thetaNat) (hdelta : 0 ≤ delta)
    (hdeltaOne : (k : ℝ) ^ 2 * delta ≤ 1)
    (hnu : 1 ≤ nu) (hB0nu : B0 ≤ nu)
    (htau : 0 ≤ tau) (htauSmall : 4 * tau * (k : ℝ) ^ 2 ≤ 1)
    (hlossGlobal : epsilon * (H : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ))
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hgamma : gamma.Admissible)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hupperAll : ∀ h : ℕ,
      h ≤ k ^ (2 * N + 1) * thetaNat →
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ h) phi gamma ≤
        (p : ℝ) ^ (((H - h : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hsection7 : ∀ {r' B' s a' b' nu' c' : ℕ}, [NeZero (p ^ B')] →
      1 ≤ r' → r' < k →
      ∀ (phi' : WooleyPolynomialSystem k)
        (gamma' : WooleySourceSequence),
        1 ≤ c' → phi'.Spaced p c' → gamma'.Admissible →
        WooleySection9Admissible k r' B' a' b' nu' B0 tau epsilon →
        wooleySourcePolynomialMixedMean phi' s r' p B' a' b' nu' gamma' ≤
          C * (p : ℝ) ^ (k ^ 2 * nu') *
            wooleySourcePolynomialMixedMean phi' s r' p B'
              (wooleyNextB k r' b') b' nu' gamma')
    (hnode : ∀ m b : ℕ, m < N → b ≤ k ^ (2 * m) * thetaNat →
      (k : ℝ) ^ 2 * (delta * (thetaNat : ℝ)) ≤ (b : ℝ) →
      WooleySection10NodeHierarchy k B H nu thetaNat m b
        Lambda delta tau epsilon) :
    WooleyIterationChain k p Lambda (C ^ ((2 * k : ℕ) : ℝ))
      delta (thetaNat : ℝ)
      (fun r' a' b' => wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r' a' b' nu Lambda gamma)
      N thetaNat thetaNat 1 := by
  apply wooley_iterationChain_exists_bounded
    (N := N) (m := 0) (q := thetaNat) (by simp)
  · intro m a b r hmN hbUpper hstateA hstateB hstateRel hr hrk
    rcases hnode m b hmN hbUpper hstateB with
      ⟨hbUpper', hscaleNu, hscaleB, hscaleH,
        hcurrentMargin, hsecondMargin, hepsilonSmall, hhierarchy⟩
    apply wooleySourcePolynomial_iterationStep_of_scale_hierarchy
      phi gamma C Lambda delta (thetaNat : ℝ) tau epsilon
      hpPrime hk hC hLambda hr hrk
    · exact mul_nonneg hdelta (by positivity)
    · exact hstateA
    · exact hstateB
    · exact hstateRel
    · exact hnu
    · exact hB0nu
    · exact hscaleNu
    · exact hscaleB
    · exact hscaleH
    · exact htau
    · exact htauSmall
    · exact hcurrentMargin
    · exact hsecondMargin
    · exact hepsilonSmall
    · exact hlossGlobal
    · exact hphi
    · exact hc
    · exact hgamma
    · exact hscale
    · intro h hh
      apply hupperAll h
      calc
        h ≤ k * b := hh
        _ ≤ k * (k ^ (2 * m) * thetaNat) :=
          Nat.mul_le_mul_left k hbUpper
        _ = k ^ (2 * m + 1) * thetaNat := by
          rw [pow_succ']
          ring
        _ ≤ k ^ (2 * N + 1) * thetaNat := by
          exact Nat.mul_le_mul_right thetaNat
            (Nat.pow_le_pow_right (by omega : 1 ≤ k) (by omega))
    · exact hsection7
    · exact hhierarchy
  · simp
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hkSq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hdeltaLe : delta ≤ 1 :=
      (show delta ≤ (k : ℝ) ^ 2 * delta by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hkSq hdelta).trans
          hdeltaOne
    have hscaled : delta * (thetaNat : ℝ) ≤
        1 * (thetaNat : ℝ) :=
      mul_le_mul_of_nonneg_right hdeltaLe (Nat.cast_nonneg thetaNat)
    simpa only [one_mul] using hscaled
  · simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hdeltaOne
        (show (0 : ℝ) ≤ (thetaNat : ℝ) by positivity)
  · simp only [one_mul, show k - 1 + 1 = k by omega]
    exact Nat.le_mul_of_pos_left thetaNat (by omega)
  · omega
  · omega

#print axioms wooley_section10_first_loss_from_global
#print axioms wooley_section10_second_loss_from_global
#print axioms wooleySourcePolynomial_iterationStep_of_scale_hierarchy
#print axioms WooleySection10NodeHierarchy
#print axioms wooleySection10NodeHierarchy_of_global
#print axioms wooleySourcePolynomial_iterationChain_of_hierarchy_ledger

end

end GafniTao
