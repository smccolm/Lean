import GafniTao.Pintz2023Equation42Horizontal

/-!
# Pintz (2023), equation (4.2): completed residue-bearing shift

The theorem in this file has no analytic side-condition parameters.  It
combines absolute integrability of both complete vertical lines, uniform
decay of both horizontal edges, and the finite residue theorem.  The contour
is shifted from `Re s = 3` to the source line `Re s = -eta`, crossing exactly
the translated zeta pole at `s = 1-rho`.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

set_option maxHeartbeats 800000

/-- The exact complete-line displacement used in Pintz (2023), equation
(4.2), with the translated zeta-pole residue retained explicitly. -/
theorem pintz2023Equation42_complete_source_shift
    {X : ℕ} {rho : ℂ} {lambda eta : ℝ}
    (hrhoZero : riemannZeta rho = 0)
    (hrhoLower : 1 / 2 ≤ rho.re) (hrhoUpper : rho.re < 1)
    (hlambda : 0 < lambda) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 4) :
    pintz2023Equation42Integral X rho lambda =
      VerticalIntegral'
        (pintz2023Equation42Integrand X rho lambda) (-eta) +
          pintz2023PoleResidue X rho lambda := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hsigmaLower : 1 / 4 ≤ rho.re + (-eta) := by linarith
  have hsigmaUpper : rho.re + (-eta) < 1 := by linarith
  have hleftLower : -3 ≤ -eta := by linarith
  have hleftUpper : -eta ≤ 3 := by linarith
  apply pintz2023Equation42_complete_shift
    hrhoOne hrhoZero (by linarith) (by linarith) (by linarith)
  · exact integrable_pintz2023Equation42Integrand_three hrhoLower hlambda
  · exact integrable_pintz2023Equation42Integrand_left hlambda
      (by linarith) hsigmaLower hsigmaUpper
  · exact tendsto_pintz2023Equation42_HIntegral'_neg_zero hlambda
      hleftLower hleftUpper hsigmaLower
  · exact tendsto_pintz2023Equation42_HIntegral'_zero hlambda
      hleftLower hleftUpper hsigmaLower

#print axioms pintz2023Equation42_complete_source_shift

end

end GafniTao
