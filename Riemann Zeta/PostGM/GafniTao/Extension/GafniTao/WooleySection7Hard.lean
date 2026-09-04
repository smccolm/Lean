import GafniTao.WooleyEquation724
import GafniTao.WooleySection7HardPower

/-!
# The hard branch of Wooley Lemma 7.1

This file applies the lower-degree Corollary 3.2 to the literal translated
coefficient sequence, invokes equations (7.18)--(7.23), sums by (7.24), and
uses the complete exponent ledger.  The Corollary 3.2 constant remains
explicit, as required by its uniform big-O meaning.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleySourcePolynomial_section7_hard_of_lower_bound
    {k r p B s a b nu c : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r) (hrk : r < k)
    (hkp : k < p) (hnu : 1 ≤ nu) (hnua : nu ≤ a)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : ∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a)
    (hBPrime : ∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (gamma : WooleySourceSequence) (hgamma : gamma.Admissible)
    (tau epsilon C : ℝ) (hC : 0 < C) (B0 : ℕ)
    (hcor : ∀ (BPrime : ℕ) (Psi : WooleyPolynomialSystem r)
        (coeff : WooleySourceSequence),
      B0 ≤ BPrime → Psi.InPhiTau p BPrime tau → coeff.Admissible →
        wooleySourcePolynomialMean (wooleyTriangular r) (p ^ BPrime)
            Psi coeff ≤
          C * (p ^ BPrime : ℝ) ^ (epsilon ^ 2) *
            wooleySourcePolynomialConditionedMean
              (wooleyTriangular r) (p ^ BPrime)
              (p ^ (BPrime ⌈/⌉ r)) Psi coeff)
    (hPhiTau : ∀ gammaVal : ℕ, gammaVal < nu →
      tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
        (a - (k - r) * gammaVal : ℕ))
    (hEpsilonZero :
      (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
        (nu : ℝ))
    (hB0 : ∀ gammaVal : ℕ, gammaVal < nu →
      B0 ≤ wooleySection7BPrimeNat k r a b gammaVal) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      C * (p : ℝ) ^ (k ^ 2 * nu) *
        wooleySourcePolynomialMixedMean phi s r p B
          (wooleySection7NextB k r b) b nu gamma := by
  have haNext : a ≤ wooleySection7NextB k r b := by
    exact (wooley_section7_a_add_HPrime_le_nextB hr
      (hBPrime 0 (by omega))).trans' (Nat.le_add_right a _)
  apply wooley_equation_7_24_of_local phi gamma hnua haNext
    (C * (p : ℝ) ^ (k ^ 2 * nu)) (by positivity)
  intro xi eta hseparated hxiMass hetaMass
  have hpoint : ∀ (gammaVal : ℕ), gammaVal < nu →
      ∀ (Psi : WooleyPolynomialSystem r),
        Psi.Spaced p (a - (k - r) * gammaVal) →
        ∀ alpha : Fin k → ZMod (p ^ B),
          wooleySourcePolynomialMean (wooleyTriangular r)
              (p ^ wooleySection7BPrimeNat k r a b gammaVal) Psi
              (wooleySourceTwist
                (wooleyAffinePullback gamma (p ^ a)
                  (pow_pos hpPrime.pos a) (xi.val : ℤ))
                (fun n => wooleySourcePolynomialPhase
                  (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
                  alpha n)) ≤
            C * (p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) ^
                (epsilon ^ 2) *
              wooleySourcePolynomialConditionedMean (wooleyTriangular r)
                (p ^ wooleySection7BPrimeNat k r a b gammaVal)
                (p ^ wooleySection7HPrime k r a b gammaVal) Psi
                (wooleySourceTwist
                  (wooleyAffinePullback gamma (p ^ a)
                    (pow_pos hpPrime.pos a) (xi.val : ℤ))
                  (fun n => wooleySourcePolynomialPhase
                    (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
                    alpha n)) := by
    intro gammaVal hgammaVal Psi hPsi alpha
    let coeff := wooleySection7Coefficient phi gamma p a hpPrime.pos
      (xi.val : ℤ) alpha
    have hPhi : Psi.InPhiTau p
        (wooleySection7BPrimeNat k r a b gammaVal) tau :=
      ⟨a - (k - r) * gammaVal, hPsi, hPhiTau gammaVal hgammaVal⟩
    have hbound := hcor
      (wooleySection7BPrimeNat k r a b gammaVal) Psi coeff
      (hB0 gammaVal hgammaVal) hPhi
      (hgamma.section7Coefficient phi p a hpPrime.pos (xi.val : ℤ) alpha)
    have hbase :
        (p ^ wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
          (p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) := by
      norm_cast
      exact Nat.pow_le_pow_right hpPrime.pos
        wooley_section7_BPrimeNat_le_zero
    have hloss := Real.rpow_le_rpow (by positivity) hbase (sq_nonneg epsilon)
    have hcond : 0 ≤ wooleySourcePolynomialConditionedMean
        (wooleyTriangular r)
        (p ^ wooleySection7BPrimeNat k r a b gammaVal)
        (p ^ wooleySection7HPrime k r a b gammaVal) Psi coeff := by
      unfold wooleySourcePolynomialConditionedMean
      split_ifs
      · simp
      · exact mul_nonneg
          (inv_nonneg.mpr (wooleySourceMassSq_nonneg coeff))
          (Finset.sum_nonneg fun zeta hzeta => mul_nonneg
            (wooleySourceResidueMassSq_nonneg coeff _ zeta)
            (mul_nonneg (by positivity)
              (Finset.sum_nonneg fun alphaPrime halphaPrime =>
                pow_nonneg (norm_nonneg _) _)))
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hloss hC.le) hcond
    exact hbound.trans (by
      simpa only [coeff, wooleySection7Coefficient] using hscaled)
  obtain ⟨gammaVal, hgammaVal, hlocal⟩ :=
    wooley_equation_7_23_native hpPrime hc hr hrk hkp hMB hgammaK
      hBPrime phi hphi gamma xi eta hseparated hxiMass hetaMass
      C ((p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) ^
        (epsilon ^ 2)) (by positivity) hpoint
  let fiberSum : ℝ :=
    ∑ xiPrime ∈ wooleyResidueRefinementFiber p a
        (wooleySection7NextB k r b)
        ((Nat.le_add_right a (wooleySection7HPrime k r a b gammaVal)).trans
          (wooley_section7_a_add_HPrime_le_nextB hr
            (hBPrime gammaVal hgammaVal))) xi,
      wooleySourceResidueMassSq gamma
          (p ^ wooleySection7NextB k r b) xiPrime *
        wooleySourcePolynomialMixedResidueMoment phi s r p B
          (wooleySection7NextB k r b) b gamma xiPrime eta
  have hpower := wooley_section7_hard_power_loss_zero hpPrime.two_le hr hrk hnu
    hgammaVal (hBPrime gammaVal hgammaVal)
    hEpsilonZero
  have hsum : 0 ≤ fiberSum := by
    dsimp only [fiberSum]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg
      (wooleySourceResidueMassSq_nonneg gamma _ _)
      (wooleySourcePolynomialMixedResidueMoment_nonneg
        phi s r p B (wooleySection7NextB k r b) b gamma _ eta)
  have hcoeff :
      C * ((p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) ^
          (epsilon ^ 2) *
        (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
            wooleyTriangular r) ≤
        C * (p : ℝ) ^ (k ^ 2 * nu) :=
    mul_le_mul_of_nonneg_left hpower hC.le
  have hscaled := mul_le_mul_of_nonneg_right hcoeff hsum
  calc
    wooleySourceResidueMassSq gamma (p ^ a) xi *
        wooleySourcePolynomialMixedResidueMoment
          phi s r p B a b gamma xi eta ≤
      C * (p ^ wooleySection7BPrimeNat k r a b 0 : ℝ) ^
          (epsilon ^ 2) *
        (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
            wooleyTriangular r * fiberSum := by
      simpa only [fiberSum] using hlocal
    _ ≤ (C * (p : ℝ) ^ (k ^ 2 * nu)) * fiberSum := by
      simpa only [mul_assoc] using hscaled

/-- Existential-constant wrapper obtained directly from the lower-degree
Corollary 3.2. -/
theorem wooleySourcePolynomial_section7_hard
    {k r p B s a b nu c : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r) (hrk : r < k)
    (hkp : k < p) (hnu : 1 ≤ nu) (hnua : nu ≤ a)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : ∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a)
    (hBPrime : ∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (gamma : WooleySourceSequence) (hgamma : gamma.Admissible)
    (hlower : WooleyPolynomialCorollary32At r p)
    (tau epsilon : ℝ) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (hPhiTau : ∀ gammaVal : ℕ, gammaVal < nu →
      tau * (wooleySection7BPrimeNat k r a b gammaVal : ℝ) ≤
        (a - (k - r) * gammaVal : ℕ))
    (hEpsilonZero :
      (wooleySection7BPrimeNat k r a b 0 : ℝ) * epsilon ^ 2 <
        (nu : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      (∀ gammaVal : ℕ, gammaVal < nu →
        B0 ≤ wooleySection7BPrimeNat k r a b gammaVal) →
      wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
        C * (p : ℝ) ^ (k ^ 2 * nu) *
          wooleySourcePolynomialMixedMean phi s r p B
            (wooleySection7NextB k r b) b nu gamma := by
  obtain ⟨C, hC, B0, hcor⟩ :=
    hlower tau (epsilon ^ 2) htau (sq_pos_of_pos hepsilon)
  refine ⟨C, hC, B0, fun hB0 => ?_⟩
  exact wooleySourcePolynomial_section7_hard_of_lower_bound
    hpPrime hc hr hrk hkp hnu hnua hMB hgammaK hBPrime phi hphi gamma
    hgamma tau epsilon C hC B0 hcor hPhiTau hEpsilonZero hB0

#print axioms wooleySourcePolynomial_section7_hard_of_lower_bound
#print axioms wooleySourcePolynomial_section7_hard

end

end GafniTao
