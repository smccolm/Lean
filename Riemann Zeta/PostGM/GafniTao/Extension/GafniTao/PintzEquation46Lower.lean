import GafniTao.PintzContourBounds

/-!
# Pintz equation (4.6): quantitative detector lower bound

The exact contour identity and all three explicit error pieces are assembled
here into the lower bound that drives the zero-density selection argument.
-/

open Complex Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The complete explicit error majorant used for equation (4.6). -/
noncomputable def pintzEquation46ErrorBound
    (etaJ gamma lambda Zminus Zplus : ℝ) : ℝ :=
  pintzEquation46RightTailBound etaJ gamma lambda +
    pintzEquation46HorizontalBound lambda Zminus +
    pintzEquation46HorizontalBound lambda Zplus

/-- Source-faithful lower bound following equation (4.6).  The hypothesis
that the displayed explicit error is at most `1/4` is subsequently discharged
from the `M₁` estimate; it is not a theorem-equivalent assumption. -/
theorem one_quarter_le_norm_pintzEquation46Integral
    {Delta eta etaJ gamma lambda Zminus Zplus : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (heta : eta <= 1 / 4)
    (hxi : pintzXi Delta eta <= 1 / 2)
    (hlambda : pintzMobiusLambdaThreshold <= lambda)
    (hheight : 2 * lambda < |gamma|)
    (hleftLower : -3 <= pintzLeftEdge Delta eta etaJ)
    (hleftUpper : pintzLeftEdge Delta eta etaJ <= 3)
    (hZminusNonneg : 0 <= Zminus) (hZplusNonneg : 0 <= Zplus)
    (hZminus : ∀ x ∈ Set.Icc (pintzLeftEdge Delta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ gamma +
        ((x : ℂ) + ((-2 * lambda : ℝ) : ℂ) * I))‖ <= Zminus)
    (hZplus : ∀ x ∈ Set.Icc (pintzLeftEdge Delta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ gamma +
        ((x : ℂ) + ((2 * lambda : ℝ) : ℂ) * I))‖ <= Zplus)
    (herror : pintzEquation46ErrorBound etaJ gamma lambda
      Zminus Zplus <= 1 / 4) :
    1 / 4 <= ‖pintzEquation46Integral Delta eta etaJ gamma lambda‖ := by
  have hrhoNear : 1 - eta <= (pintzRho etaJ gamma).re := by
    simp [pintzRho]
    unfold pintzDeltaJ at hdeltaJ
    linarith
  have hrhoHalf : 1 / 2 <= (pintzRho etaJ gamma).re := by
    simp [pintzRho]
    unfold pintzDeltaJ at hdeltaJ
    unfold pintzXi at hxi
    linarith
  have hhead : 1 / 2 <=
      ‖pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda‖ :=
    one_half_le_norm_pintzMobiusFiniteHead_of_large
      hrhoHalf hrhoNear hlambda heta
  have hexact := pintz_equation_4_6_exact
    hrhoZero hrhoHalf
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8)
        (pintzMobiusLambdaThreshold_ge_eight.trans hlambda))
      hDelta hdeltaJ hheight
  have herr := norm_pintzEquation46ContourError_le
    hrhoZero
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8)
        (pintzMobiusLambdaThreshold_ge_eight.trans hlambda))
      hleftLower hleftUpper hDelta.le hdeltaJ hxi
      hZminusNonneg hZplusNonneg hZminus hZplus
  have herrQuarter :
      ‖pintzEquation46ContourError Delta eta etaJ gamma lambda‖ <= 1 / 4 :=
    herr.trans (by simpa [pintzEquation46ErrorBound] using herror)
  have htriangle :
      ‖pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda‖ <=
        ‖pintzEquation46Integral Delta eta etaJ gamma lambda‖ +
          ‖pintzEquation46ContourError Delta eta etaJ gamma lambda‖ := by
    rw [hexact]
    exact norm_add_le _ _
  linarith

#print axioms one_quarter_le_norm_pintzEquation46Integral

end

end GafniTao
