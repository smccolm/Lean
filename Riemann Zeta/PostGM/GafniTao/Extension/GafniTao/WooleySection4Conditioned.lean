import GafniTao.WooleySection4Insertion
import GafniTao.WooleySection7ConditionedExpansion

/-!
# Conditioned form of Wooley equations (4.13)--(4.14)

This file expands the lower-modulus conditioned mean of the exact
alpha-twisted coefficients, applies the same redundant-congruence identity
on every refined residue class, and removes the inserted grid.  It is the
formal counterpart of the paragraph following (4.14).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The alpha average of the conditioned lower-system means in (4.13). -/
def wooleySection4ConditionedInsertedAverage {k : ℕ}
    (theta Psi : WooleyPolynomialSystem k)
    (q qPrime qH s : ℕ) [NeZero q] [NeZero qPrime] [NeZero qH]
    (gamma : WooleySourceSequence) : ℝ :=
  (((q ^ k : ℕ) : ℝ)⁻¹) *
    ∑ alpha : Fin k → ZMod q,
      wooleySourcePolynomialConditionedMean s qPrime qH Psi
        (wooleySourceTwist gamma
          (fun n => wooleySourcePolynomialPhase theta alpha n))

/-- Expanding the conditioned lower mean commutes with the outer alpha
average.  Every residue mass is retained explicitly. -/
theorem wooleySection4ConditionedInsertedAverage_expand
    {k q qPrime qH s : ℕ}
    [NeZero q] [NeZero qPrime] [NeZero qH]
    (theta Psi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence)
    (hmass : wooleySourceMassSq gamma ≠ 0) :
    wooleySourceMassSq gamma *
        wooleySection4ConditionedInsertedAverage
          theta Psi q qPrime qH s gamma =
      ∑ zeta : ZMod qH,
        wooleySourceResidueMassSq gamma qH zeta *
          ((((q ^ k : ℕ) : ℝ)⁻¹) *
            ∑ alpha : Fin k → ZMod q,
              wooleySourcePolynomialMean s qPrime Psi
                (wooleySourceTwist
                  (wooleySourceResidueSequence gamma qH zeta)
                  (fun n => wooleySourcePolynomialPhase theta alpha n))) := by
  unfold wooleySection4ConditionedInsertedAverage
  have hexpand (alpha : Fin k → ZMod q) :=
    wooleySourcePolynomialConditionedMean_polynomialTwist_expand
      (qPrime := qPrime) (qH := qH) (R := s)
      theta Psi gamma alpha hmass
  calc
    wooleySourceMassSq gamma *
        ((((q ^ k : ℕ) : ℝ)⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            wooleySourcePolynomialConditionedMean s qPrime qH Psi
              (wooleySourceTwist gamma
                (fun n => wooleySourcePolynomialPhase theta alpha n))) =
      (((q ^ k : ℕ) : ℝ)⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          wooleySourceMassSq gamma *
            wooleySourcePolynomialConditionedMean s qPrime qH Psi
              (wooleySourceTwist gamma
                (fun n => wooleySourcePolynomialPhase theta alpha n)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring
    _ = (((q ^ k : ℕ) : ℝ)⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ zeta : ZMod qH,
            wooleySourceResidueMassSq gamma qH zeta *
              wooleySourcePolynomialMean s qPrime Psi
                (wooleySourceTwist
                  (wooleySourceResidueSequence gamma qH zeta)
                  (fun n => wooleySourcePolynomialPhase theta alpha n)) := by
      apply congrArg (fun x : ℝ => ((q ^ k : ℕ) : ℝ)⁻¹ * x)
      apply Finset.sum_congr rfl
      intro alpha halpha
      exact hexpand alpha
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro zeta hzeta
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring

/-- Equation (4.14) after the lower critical-exponent estimate: the
conditioned inserted average is exactly the original system conditioned at
the refined level.  The congruence removal is proved on every actual source
residue sequence. -/
theorem wooleySection4_conditionedInsertedAverage_eq_of_equation_4_12
    {k p B h H s : ℕ}
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ (B - k * h))]
    [NeZero (p ^ (H - h))]
    (theta Psi : WooleyPolynomialSystem k)
    (h412 : ∀ gamma : WooleySourceSequence,
      wooleySourcePolynomialMean s (p ^ B) theta gamma =
        ((((p ^ B) ^ k : ℕ) : ℝ)⁻¹) *
          ∑ alpha : Fin k → ZMod (p ^ B),
            wooleySourcePolynomialMean s (p ^ (B - k * h)) Psi
              (wooleySourceTwist gamma
                (fun n => wooleySourcePolynomialPhase theta alpha n))) :
    ∀ gamma : WooleySourceSequence,
      wooleySection4ConditionedInsertedAverage
          theta Psi (p ^ B) (p ^ (B - k * h)) (p ^ (H - h)) s gamma =
        wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ (H - h))
          theta gamma := by
  intro gamma
  by_cases hmass : wooleySourceMassSq gamma = 0
  · have hleft : wooleySection4ConditionedInsertedAverage
        theta Psi (p ^ B) (p ^ (B - k * h)) (p ^ (H - h)) s gamma = 0 := by
      unfold wooleySection4ConditionedInsertedAverage
      have hterm : ∀ alpha : Fin k → ZMod (p ^ B),
          wooleySourcePolynomialConditionedMean s (p ^ (B - k * h))
            (p ^ (H - h)) Psi
            (wooleySourceTwist gamma
              (fun n => wooleySourcePolynomialPhase theta alpha n)) = 0 := by
        intro alpha
        unfold wooleySourcePolynomialConditionedMean
        rw [wooleySourceMassSq_twist]
        · simp [hmass]
        · exact fun n => wooleySourcePolynomialPhase_norm theta alpha n
      simp_rw [hterm]
      simp
    have hright : wooleySourcePolynomialConditionedMean s (p ^ B)
        (p ^ (H - h)) theta gamma = 0 := by
      simp [wooleySourcePolynomialConditionedMean, hmass]
    rw [hleft, hright]
  · have hexpand := wooleySection4ConditionedInsertedAverage_expand
      (q := p ^ B) (qPrime := p ^ (B - k * h))
      (qH := p ^ (H - h)) (s := s) theta Psi gamma hmass
    have h412Residue (zeta : ZMod (p ^ (H - h))) :
        ((((p ^ B) ^ k : ℕ) : ℝ)⁻¹) *
            ∑ alpha : Fin k → ZMod (p ^ B),
              wooleySourcePolynomialMean s (p ^ (B - k * h)) Psi
                (wooleySourceTwist
                  (wooleySourceResidueSequence gamma (p ^ (H - h)) zeta)
                  (fun n => wooleySourcePolynomialPhase theta alpha n)) =
          wooleySourcePolynomialMean s (p ^ B) theta
            (wooleySourceResidueSequence gamma (p ^ (H - h)) zeta) := by
      symm
      exact h412
        (wooleySourceResidueSequence gamma (p ^ (H - h)) zeta)
    have hexpand' : wooleySourceMassSq gamma *
        wooleySection4ConditionedInsertedAverage
          theta Psi (p ^ B) (p ^ (B - k * h)) (p ^ (H - h)) s gamma =
      ∑ zeta : ZMod (p ^ (H - h)),
        wooleySourceResidueMassSq gamma (p ^ (H - h)) zeta *
          wooleySourcePolynomialMean s (p ^ B) theta
            (wooleySourceResidueSequence gamma (p ^ (H - h)) zeta) := by
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro zeta hzeta
      rw [h412Residue]
    have hconditioned :=
      wooleySourcePolynomialConditionedMean_polynomialTwist_expand
        (q := p ^ B) (qPrime := p ^ B) (qH := p ^ (H - h))
        (R := s) theta theta gamma (0 : Fin k → ZMod (p ^ B)) hmass
    have hzeroPhase : ∀ n : ℤ,
        wooleySourcePolynomialPhase theta (0 : Fin k → ZMod (p ^ B)) n = 1 :=
      wooleySourcePolynomialPhase_zero theta
    have htwist (zeta : ZMod (p ^ (H - h))) :
        wooleySourceTwist
            (wooleySourceResidueSequence gamma (p ^ (H - h)) zeta)
            (fun n => wooleySourcePolynomialPhase theta
              (0 : Fin k → ZMod (p ^ B)) n) =
          wooleySourceResidueSequence gamma (p ^ (H - h)) zeta := by
      ext n
      simp [wooleySourceTwist_apply, hzeroPhase]
    have htwistOuter :
        wooleySourceTwist gamma
            (fun n => wooleySourcePolynomialPhase theta
              (0 : Fin k → ZMod (p ^ B)) n) = gamma := by
      ext n
      simp [wooleySourceTwist_apply, hzeroPhase]
    simp_rw [htwist] at hconditioned
    rw [htwistOuter] at hconditioned
    have hmul : wooleySourceMassSq gamma *
        wooleySection4ConditionedInsertedAverage
          theta Psi (p ^ B) (p ^ (B - k * h)) (p ^ (H - h)) s gamma =
        wooleySourceMassSq gamma *
          wooleySourcePolynomialConditionedMean s (p ^ B)
            (p ^ (H - h)) theta gamma := by
      rw [hexpand']
      exact hconditioned.symm
    exact (mul_left_cancel₀ hmass hmul)

/-- Equation (4.14) after the lower critical-exponent estimate, with the
normalizing system produced by equation (4.12). -/
theorem wooleySection4_conditionedInsertedAverage_eq
    {k p c B h H s : ℕ}
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ (B - k * h))]
    [NeZero (p ^ (H - h))]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hkhB : k * h ≤ B)
    (hs : 1 ≤ s)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (xi : ℤ) :
    ∃ Psi : WooleyPolynomialSystem k,
      Psi.Spaced p (c + h) ∧
      ∀ gamma : WooleySourceSequence,
        wooleySection4ConditionedInsertedAverage
            (wooleyAffinePolynomialSystem phi (p ^ h) xi) Psi
            (p ^ B) (p ^ (B - k * h)) (p ^ (H - h)) s gamma =
          wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ (H - h))
            (wooleyAffinePolynomialSystem phi (p ^ h) xi) gamma := by
  obtain ⟨Psi, hPsi, h412⟩ := wooleySourcePolynomial_equation_4_12
    hpPrime hc hkhB hs phi hphi xi
  exact ⟨Psi, hPsi,
    wooleySection4_conditionedInsertedAverage_eq_of_equation_4_12
      (B := B) (h := h) (H := H) (s := s)
      (wooleyAffinePolynomialSystem phi (p ^ h) xi) Psi h412⟩

#print axioms wooleySection4ConditionedInsertedAverage_expand
#print axioms wooleySection4_conditionedInsertedAverage_eq_of_equation_4_12
#print axioms wooleySection4_conditionedInsertedAverage_eq

end

end GafniTao
