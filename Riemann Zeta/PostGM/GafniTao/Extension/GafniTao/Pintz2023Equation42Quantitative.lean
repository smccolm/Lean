import GafniTao.Pintz2023Equation42ResidueBound

/-!
# Pintz (2023), equation (4.2): quantitative source form

This file assembles the completed contour shift with the translated-pole
estimate for the source zero coordinate `rho_j = 1-eta_j+i gamma_j`.  No
integrability or horizontal-edge hypotheses remain in the public statement.
-/

open Complex MeasureTheory Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The exact residue identity behind the error term in Pintz's equation
(4.2), specialized to a zero written as `1-etaJ+i*gamma`. -/
theorem pintz2023Equation42_source_shift
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 0 < lambda) (hetaUpper : eta ≤ 1 / 4) :
    pintz2023Equation42Integral X (pintz2023Rho etaJ gamma) lambda =
      VerticalIntegral'
        (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
        (-eta) +
      pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda := by
  apply pintz2023Equation42_complete_source_shift hrhoZero
  · simp [pintz2023Rho]
    linarith
  · simp [pintz2023Rho]
    linarith
  · exact hlambda
  · exact hetaJPos.trans_le hetaJ
  · exact hetaUpper

/-- Pintz's equation-(4.2) displacement, with the complete left vertical
integral and every translated-pole factor explicit. -/
theorem norm_pintz2023Equation42_sub_left_le
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 0 < lambda) (hetaUpper : eta ≤ 1 / 4)
    (hgamma : gamma ≠ 0) :
    ‖pintz2023Equation42Integral X (pintz2023Rho etaJ gamma) lambda -
        VerticalIntegral'
          (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
          (-eta)‖ ≤
      (harmonic X : ℝ) * |gamma|⁻¹ *
        Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) := by
  have hshift := pintz2023Equation42_source_shift (X := X) hrhoZero
    hetaJPos hetaJ hlambda hetaUpper
  have hdiff :
      pintz2023Equation42Integral X (pintz2023Rho etaJ gamma) lambda -
          VerticalIntegral'
            (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
            (-eta) =
        pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda := by
    rw [hshift]
    abel
  rw [hdiff]
  exact norm_pintz2023PoleResidue_le_eta hlambda hgamma hetaJPos.le hetaJ

/-- Exact conversion of the residue exponential to Pintz's `Y = exp lambda`
normalization.  The small uniform factor `exp (eta^2/lambda)` is deliberately
retained rather than hidden in `O`-notation. -/
theorem pintz2023_residue_exponential_eq
    (eta gamma lambda : ℝ) :
    Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) =
      Real.exp (eta ^ 2 / lambda) *
        (Real.exp lambda) ^ eta *
          Real.exp (-gamma ^ 2 / lambda) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos lambda), Real.log_exp]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Equation (4.2) in the paper's `Y = exp lambda` notation, still with an
explicit uniform residue constant. -/
theorem norm_pintz2023Equation42_sub_left_le_sourceY
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintz2023Rho etaJ gamma) = 0)
    (hetaJPos : 0 < etaJ) (hetaJ : etaJ ≤ eta)
    (hlambda : 0 < lambda) (hetaUpper : eta ≤ 1 / 4)
    (hgamma : gamma ≠ 0) :
    ‖pintz2023Equation42Integral X (pintz2023Rho etaJ gamma) lambda -
        VerticalIntegral'
          (pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda)
          (-eta)‖ ≤
      ((harmonic X : ℝ) * Real.exp (eta ^ 2 / lambda)) *
        (Real.exp lambda) ^ eta * |gamma|⁻¹ *
          Real.exp (-gamma ^ 2 / lambda) := by
  calc
    _ ≤ (harmonic X : ℝ) * |gamma|⁻¹ *
          Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) :=
      norm_pintz2023Equation42_sub_left_le hrhoZero hetaJPos hetaJ
        hlambda hetaUpper hgamma
    _ = _ := by
      rw [pintz2023_residue_exponential_eq]
      ring

#print axioms pintz2023Equation42_source_shift
#print axioms norm_pintz2023Equation42_sub_left_le
#print axioms pintz2023_residue_exponential_eq
#print axioms norm_pintz2023Equation42_sub_left_le_sourceY

end

end GafniTao
