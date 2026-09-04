import GafniTao.WooleySection7ShiftedMoment
import GafniTao.WooleySection7Coefficient
import GafniTao.WooleyPadicSeparation
import GafniTao.WooleySourceMixed

/-!
# The local source mixed moment in Wooley Section 7

This file applies the arbitrary-residue equation-(7.17) identity to the
literal residue-class pullbacks occurring in `K^r_{a,b}`.  It is the bridge
from the congruence calculation to equation (7.18).
-/

namespace GafniTao

noncomputable section

/-- The local mixed residue moment is exactly the normalized mixed average
of the two affine pullbacks. -/
theorem wooleySourcePolynomialMixedResidueMoment_eq_pullbackAverage
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) :
    wooleySourcePolynomialMixedResidueMoment
        phi s r p B a b gamma xi eta =
      wooleySourceNormalizedMixedRealAverage
        (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
        (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
        (p ^ B) (wooleyTriangular r) (s - wooleyTriangular r)
        (wooleyAffinePullback gamma (p ^ a)
          (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) a) (xi.val : ℤ))
        (wooleyAffinePullback gamma (p ^ b)
          (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) b) (eta.val : ℤ)) := by
  unfold wooleySourcePolynomialMixedResidueMoment
    wooleySourceNormalizedMixedRealAverage
  simp_rw [wooleySourceNormalizedPolynomialSum_affinePullback]
  simp

/-- Exact local equation (7.18) for a separated pair of nonzero-mass source
residue classes.  The valuation `gammaVal` and unit `omegaVal` are extracted
from the actual residue representatives, rather than supplied independently.
-/
theorem wooley_equation_7_18_local_native
    {k r p c a b B nu s : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : ∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a)
    (hBPrime : ∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (gamma : WooleySourceSequence)
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b))
    (hseparated : wooleyResiduesSeparated nu xi eta)
    (hxiMass : wooleySourceResidueMassSq gamma (p ^ a) xi ≠ 0)
    (hetaMass : wooleySourceResidueMassSq gamma (p ^ b) eta ≠ 0) :
    ∃ (gammaVal : ℕ) (Psi : WooleyPolynomialSystem r),
      gammaVal < nu ∧
      Psi.Spaced p (a - (k - r) * gammaVal) ∧
      wooleySourcePolynomialMixedResidueMoment
          phi s r p B a b gamma xi eta =
        wooleySourceInsertedNormalizedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
          (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gammaVal)
          (wooleyTriangular r) (s - wooleyTriangular r)
          (wooleyAffinePullback gamma (p ^ a)
            (pow_pos hpPrime.pos a) (xi.val : ℤ))
          (wooleyAffinePullback gamma (p ^ b)
            (pow_pos hpPrime.pos b) (eta.val : ℤ)) := by
  obtain ⟨gammaVal, omegaVal, hgammaVal, hcop, hfactor⟩ :=
    wooley_padic_separation hpPrime hseparated
  have hdiff : (xi.val : ℤ) - (eta.val : ℤ) ≠ 0 := by
    simpa only [wooleyResidueDifference] using
      (wooleyResidueDifference_ne_zero_of_separated hseparated)
  have homega : omegaVal ≠ 0 := by
    intro hw
    rw [hw, zero_mul] at hfactor
    exact hdiff (by simpa only [wooleyResidueDifference] using hfactor)
  let left := wooleyAffinePullback gamma (p ^ a)
    (pow_pos hpPrime.pos a) (xi.val : ℤ)
  let right := wooleyAffinePullback gamma (p ^ b)
    (pow_pos hpPrime.pos b) (eta.val : ℤ)
  have hleft : wooleySourceMassSq left ≠ 0 := by
    dsimp only [left]
    rw [wooleySourceMassSq_affinePullback]
    simpa using hxiMass
  have hright : wooleySourceMassSq right ≠ 0 := by
    dsimp only [right]
    rw [wooleySourceMassSq_affinePullback]
    simpa using hetaMass
  letI : NeZero (p ^ wooleySection7BPrimeNat k r a b gammaVal) :=
    ⟨pow_ne_zero _ hpPrime.ne_zero⟩
  obtain ⟨Psi, hPsi, hidentity⟩ :=
    wooley_equation_7_17_shifted_normalized_nonzero_native
      hpPrime hc hr hrk hkp hMB (hgammaK gammaVal hgammaVal)
        (hBPrime gammaVal hgammaVal)
        omegaVal (xi.val : ℤ) (eta.val : ℤ) homega hcop
        (by simpa only [wooleyResidueDifference] using hfactor) hdiff
        phi hphi left right hleft hright
  refine ⟨gammaVal, Psi, hgammaVal, hPsi, ?_⟩
  rw [wooleySourcePolynomialMixedResidueMoment_eq_pullbackAverage]
  exact hidentity

/-- Pointwise equation (7.19): the lower-degree Corollary 3.2 is applied to
the literal coefficient sequence `c_y(alpha)` from (7.14), with admissibility
proved from the original source sequence. -/
theorem wooley_equation_7_19_pointwise_native
    {k r p a q : ℕ} [NeZero p] [NeZero q]
    (hlower : WooleyPolynomialCorollary32At r p)
    (tau epsilon : ℝ) (htau : 0 < tau) (hepsilon : 0 < epsilon)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (hgamma : gamma.Admissible) (xi : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (BPrime : ℕ) (Psi : WooleyPolynomialSystem r)
        (alpha : Fin k → ZMod q),
        B0 ≤ BPrime → Psi.InPhiTau p BPrime tau →
          wooleySourcePolynomialMean (wooleyTriangular r) (p ^ BPrime)
              Psi (wooleySection7Coefficient
                phi gamma p a (Nat.pos_of_ne_zero (NeZero.ne p)) xi alpha) ≤
            C * (p ^ BPrime : ℝ) ^ (epsilon ^ 2) *
              wooleySourcePolynomialConditionedMean
                (wooleyTriangular r) (p ^ BPrime)
                (p ^ (BPrime ⌈/⌉ r)) Psi
                (wooleySection7Coefficient
                  phi gamma p a (Nat.pos_of_ne_zero (NeZero.ne p)) xi alpha) := by
  obtain ⟨C, hC, B0, hbound⟩ :=
    hlower tau (epsilon ^ 2) htau (sq_pos_of_pos hepsilon)
  refine ⟨C, hC, B0, ?_⟩
  intro BPrime Psi alpha hBPrime hPsi
  letI : NeZero (p ^ BPrime) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  exact hbound BPrime Psi
    (wooleySection7Coefficient phi gamma p a
      (Nat.pos_of_ne_zero (NeZero.ne p)) xi alpha)
    hBPrime hPsi
    (hgamma.section7Coefficient phi p a
      (Nat.pos_of_ne_zero (NeZero.ne p)) xi alpha)

/-- The exact outer average left after substituting Corollary 3.2 into
equation (7.18).  It retains the conditioned lower-degree mean and the
right-hand source factor pointwise in `alpha`. -/
def wooleySection7ConditionedInsertedAverage {k r : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (q qPrime qH R S : ℕ) [NeZero q] [NeZero qPrime] [NeZero qH]
    (left right : WooleySourceSequence) : ℝ :=
  ((((q ^ k : ℕ) : ℝ))⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      wooleySourcePolynomialConditionedMean R qPrime qH Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
        ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S)

/-- Equation (7.19) after integration in the outer frequency: any uniform
pointwise lower-degree concentration estimate yields the corresponding
bound for the literal inserted average. -/
theorem wooley_equation_7_19_outer_native
    {k r q qPrime qH R S : ℕ}
    [NeZero q] [NeZero qPrime] [NeZero qH]
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (left right : WooleySourceSequence)
    (C loss : ℝ)
    (hpoint : ∀ alpha : Fin k → ZMod q,
      wooleySourcePolynomialMean R qPrime Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) ≤
        C * loss *
          wooleySourcePolynomialConditionedMean R qPrime qH Psi
            (wooleySourceTwist left
              (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) :
    wooleySourceInsertedNormalizedRealAverage
        leftPhi rightPhi Psi q qPrime R S left right ≤
      C * loss * wooleySection7ConditionedInsertedAverage
        leftPhi rightPhi Psi q qPrime qH R S left right := by
  unfold wooleySourceInsertedNormalizedRealAverage
    wooleySection7ConditionedInsertedAverage
  have hscale : 0 ≤ ((((q ^ k : ℕ) : ℝ))⁻¹) := by positivity
  calc
    ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          wooleySourcePolynomialMean R qPrime Psi
              (wooleySourceTwist left
                (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S) ≤
      ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          (C * loss *
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
              (wooleySourceTwist left
                (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^ (2 * S) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply Finset.sum_le_sum
      intro alpha halpha
      exact mul_le_mul_of_nonneg_right (hpoint alpha) (by positivity)
    _ = ((((q ^ k : ℕ) : ℝ))⁻¹) * (C * loss) *
        (∑ alpha : Fin k → ZMod q,
          wooleySourcePolynomialConditionedMean R qPrime qH Psi
              (wooleySourceTwist left
              (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
            ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
              (2 * S)) := by
      have hsum :
          (∑ alpha : Fin k → ZMod q,
            (C * loss *
              wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
              ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                (2 * S)) =
            (C * loss) *
              ∑ alpha : Fin k → ZMod q,
                wooleySourcePolynomialConditionedMean R qPrime qH Psi
                    (wooleySourceTwist left
                      (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
                  ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                    (2 * S) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro alpha halpha
        ring
      rw [hsum]
      ring
    _ = C * loss *
        (((((q ^ k : ℕ) : ℝ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
              ‖wooleySourceNormalizedPolynomialSum rightPhi right alpha‖ ^
                (2 * S)) := by ring

#print axioms wooleySourcePolynomialMixedResidueMoment_eq_pullbackAverage
#print axioms wooley_equation_7_18_local_native
#print axioms wooley_equation_7_19_pointwise_native
#print axioms wooley_equation_7_19_outer_native

end

end GafniTao
