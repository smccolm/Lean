import GafniTao.Pintz2023LeftVerticalBound
import GafniTao.Pintz2023Detection

/-!
# Pintz (2023), equation (4.12): analytic error discharge

The three contour errors are bounded by the proved equation-(4.10), pole,
and finite-truncation estimates.  The resulting ordinate is expressed in
physical coordinates and retains the individual zero distance `etaJ`.
-/

open Complex Set

namespace GafniTao

noncomputable section

/-- The source detector with only explicit real scale inequalities left.
The constants are uniform in the zero and in all physical parameters. -/
theorem exists_pintz2023Equation412_detector_constants
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ Cleft Kremainder : ℝ,
      0 < Cleft ∧ 0 < Kremainder ∧
      ∀ (X : ℕ) (eta etaJ gamma lambda : ℝ),
        0 < X → 0 < eta → 0 < etaJ → etaJ ≤ eta →
        eta ≤ 1 / 24 → 8 ≤ lambda →
        X ≤ pintz2023Cutoff lambda →
        riemannZeta (pintz2023Rho etaJ gamma) = 0 →
        gamma ≠ 0 →
        Cleft * (X : ℝ) ^ (eta + etaJ) * (harmonic X : ℝ) *
            eta⁻¹ * (eta + etaJ)⁻¹ *
            (|gamma| + 3) ^ ((1 / 2 : ℝ) *
              (eta + etaJ) ^ (3 / 2 : ℝ) + epsilon) *
            Real.exp (eta ^ 2 / lambda - lambda * eta) *
            (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) ≤ 1 / 8 →
        (harmonic X : ℝ) * |gamma|⁻¹ *
            Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda)
              ≤ 1 / 8 →
        Kremainder * Real.exp (-2 * lambda) ≤ 1 / 8 →
        ∃ u : ℝ, |gamma - u| ≤ 2 * lambda ∧
          1 / (32 * Real.exp 2 * Real.log lambda) ≤
            ‖pintz2023TruncatedPolynomial X (pintz2023Cutoff lambda)
              (1 - etaJ + 1 / lambda) u‖ := by
  obtain ⟨Cleft, hCleft, hleft⟩ :=
    exists_norm_pintz2023Equation42_left_le hepsilon hepsilonUpper
  obtain ⟨Kremainder, hKremainder, hremainder⟩ :=
    norm_pintz2023Equation47TruncatedRemainder_le_exp_neg_two
  refine ⟨Cleft, Kremainder, hCleft, hKremainder, ?_⟩
  intro X eta etaJ gamma lambda hX heta hetaJPos hetaJLe hetaUpper hlambda
    hCutoff hzero hgamma hleftScale hpoleScale hremainderScale
  have hleftBound := hleft X eta etaJ gamma lambda hX heta hetaJPos hetaJLe
    hetaUpper (by linarith)
  have hleftEighth :
      ‖VerticalIntegral'
          (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
          (-eta)‖ ≤ 1 / 8 := hleftBound.trans hleftScale
  have hpoleBound := norm_pintz2023PoleResidue_le_eta
    (X := X) (eta := eta) (etaJ := etaJ) (gamma := gamma)
    (lambda := lambda) (by linarith) hgamma hetaJPos.le hetaJLe
  have hpoleEighth :
      ‖pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda‖ ≤
        1 / 8 := hpoleBound.trans hpoleScale
  have hrhoLower : 1 - eta ≤ (pintz2023Rho etaJ gamma).re := by
    simp [pintz2023Rho]
    linarith
  have hremainderBound := hremainder (X := X)
    (rho := pintz2023Rho etaJ gamma) (eta := eta) (lambda := lambda)
    hrhoLower hlambda hetaUpper
  have hremainderEighth :
      ‖pintz2023Equation47TruncatedRemainder X
        (pintz2023Rho etaJ gamma) lambda‖ ≤ 1 / 8 :=
    hremainderBound.trans hremainderScale
  obtain ⟨t, ht, hlarge⟩ := exists_large_pintz2023Equation47Polynomial_log
    hzero hetaJPos hetaJLe hlambda hetaUpper hX hCutoff
    hleftEighth hpoleEighth hremainderEighth
  let u : ℝ := gamma + t
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    rw [show gamma - (gamma + t) = -t by ring, abs_neg]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  · have hidentity := pintz2023Equation47Polynomial_eq_truncated
      (X := X) (etaJ := etaJ) (gamma := gamma) (lambda := lambda) (t := t) hX
    rw [hidentity] at hlarge
    simpa only [pintz2023DetectedBeta, u] using hlarge

#print axioms exists_pintz2023Equation412_detector_constants

end

end GafniTao
