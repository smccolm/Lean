import GafniTao.WooleySourceRefinement

/-!
# Expansion of the conditioned mean in Wooley equation (7.20)

The conditioned lower-degree mean is expanded over its actual residue
classes.  Multiplication by the original residue mass cancels its source
normalization, and twisting commutes exactly with restriction.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleySourcePolynomialConditionedMean_polynomialTwist_expand
    {k r q qPrime qH R : ℕ}
    [NeZero q] [NeZero qPrime] [NeZero qH]
    (leftPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (left : WooleySourceSequence) (alpha : Fin k → ZMod q)
    (hleft : wooleySourceMassSq left ≠ 0) :
    wooleySourceMassSq left *
        wooleySourcePolynomialConditionedMean R qPrime qH Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) =
      ∑ zeta : ZMod qH,
        wooleySourceResidueMassSq left qH zeta *
          wooleySourcePolynomialMean R qPrime Psi
            (wooleySourceTwist
              (wooleySourceResidueSequence left qH zeta)
              (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) := by
  have hphase : ∀ n,
      ‖wooleySourcePolynomialPhase leftPhi alpha n‖ = 1 :=
    wooleySourcePolynomialPhase_norm leftPhi alpha
  have hmassTwist :
      wooleySourceMassSq
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) =
        wooleySourceMassSq left :=
    wooleySourceMassSq_twist left _ hphase
  have hresidue (zeta : ZMod qH) :
      wooleySourceResidueMassSq
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n))
          qH zeta = wooleySourceResidueMassSq left qH zeta :=
    wooleySourceResidueMassSq_twist left _ hphase qH zeta
  have hsum (zeta : ZMod qH) (beta : Fin r → ZMod qPrime) :
      wooleySourceNormalizedPolynomialResidueSum Psi
          (wooleySourceTwist left
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n))
          beta zeta =
        wooleySourceNormalizedPolynomialSum Psi
          (wooleySourceTwist
            (wooleySourceResidueSequence left qH zeta)
            (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) beta := by
    rw [← wooleySourceNormalizedPolynomialSum_residueSequence,
      wooleySourceResidueSequence_twist]
  unfold wooleySourcePolynomialConditionedMean
    wooleySourcePolynomialMean
  rw [hmassTwist, if_neg hleft]
  simp_rw [hresidue, hsum]
  rw [← mul_assoc, mul_inv_cancel₀ hleft, one_mul]

/-- Exact equation (7.20) before the lower-degree loss factor is inserted.
The right side is a literal finite sum of the inserted averages attached to
the restricted source sequences. -/
theorem wooley_equation_7_20_expansion
    {k r q qPrime qH R S : ℕ}
    [NeZero q] [NeZero qPrime] [NeZero qH]
    (leftPhi rightPhi : WooleyPolynomialSystem k)
    (Psi : WooleyPolynomialSystem r)
    (left right : WooleySourceSequence)
    (hleft : wooleySourceMassSq left ≠ 0) :
    wooleySourceMassSq left *
        wooleySection7ConditionedInsertedAverage
          leftPhi rightPhi Psi q qPrime qH R S left right =
      ∑ zeta : ZMod qH,
        wooleySourceResidueMassSq left qH zeta *
          wooleySourceInsertedNormalizedRealAverage
            leftPhi rightPhi Psi q qPrime R S
            (wooleySourceResidueSequence left qH zeta) right := by
  unfold wooleySection7ConditionedInsertedAverage
    wooleySourceInsertedNormalizedRealAverage
  have hexpand (alpha : Fin k → ZMod q) :=
    wooleySourcePolynomialConditionedMean_polynomialTwist_expand
      (qPrime := qPrime) (qH := qH) (R := R)
      leftPhi Psi left alpha hleft
  calc
    wooleySourceMassSq left *
        (((((q ^ k : ℕ) : ℝ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
              ‖wooleySourceNormalizedPolynomialSum
                  rightPhi right alpha‖ ^ (2 * S)) =
      ((((q ^ k : ℕ) : ℝ))⁻¹) *
        (wooleySourceMassSq left *
          ∑ alpha : Fin k → ZMod q,
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
                (wooleySourceTwist left
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
              ‖wooleySourceNormalizedPolynomialSum
                  rightPhi right alpha‖ ^ (2 * S)) := by ring
    _ =
      ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          (wooleySourceMassSq left *
            wooleySourcePolynomialConditionedMean R qPrime qH Psi
              (wooleySourceTwist left
                (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
            ‖wooleySourceNormalizedPolynomialSum
                rightPhi right alpha‖ ^ (2 * S) := by
      apply congrArg (fun x : ℝ => ((((q ^ k : ℕ) : ℝ))⁻¹) * x)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring_nf
    _ = ((((q ^ k : ℕ) : ℝ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          (∑ zeta : ZMod qH,
            wooleySourceResidueMassSq left qH zeta *
              wooleySourcePolynomialMean R qPrime Psi
                (wooleySourceTwist
                  (wooleySourceResidueSequence left qH zeta)
                  (fun n => wooleySourcePolynomialPhase leftPhi alpha n))) *
            ‖wooleySourceNormalizedPolynomialSum
                rightPhi right alpha‖ ^ (2 * S) := by
      apply congrArg (fun x : ℝ => ((((q ^ k : ℕ) : ℝ))⁻¹) * x)
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [hexpand alpha]
    _ = ∑ zeta : ZMod qH,
        wooleySourceResidueMassSq left qH zeta *
          (((((q ^ k : ℕ) : ℝ))⁻¹) *
            ∑ alpha : Fin k → ZMod q,
              wooleySourcePolynomialMean R qPrime Psi
                  (wooleySourceTwist
                    (wooleySourceResidueSequence left qH zeta)
                    (fun n => wooleySourcePolynomialPhase leftPhi alpha n)) *
                ‖wooleySourceNormalizedPolynomialSum
                    rightPhi right alpha‖ ^ (2 * S)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro zeta hzeta
      ring_nf

#print axioms wooleySourcePolynomialConditionedMean_polynomialTwist_expand
#print axioms wooley_equation_7_20_expansion

end

end GafniTao
