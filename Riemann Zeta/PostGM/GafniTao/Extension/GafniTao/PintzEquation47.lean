import GafniTao.PintzFiniteContour

/-!
# Pintz equation (4.7)

This module specializes the regularized finite contour to Pintz's parameters
`δⱼ = η - ηⱼ`, `ξ = Δ + η`, and left edge `-Δ-δⱼ`.  The resulting source
factor is kept literally, including its denominator and Gaussian phase.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

def pintzDeltaJ (eta etaJ : ℝ) : ℝ := eta - etaJ

def pintzXi (Delta eta : ℝ) : ℝ := Delta + eta

def pintzLeftEdge (Delta eta etaJ : ℝ) : ℝ :=
  -Delta - pintzDeltaJ eta etaJ

noncomputable def pintzRho (etaJ gamma : ℝ) : ℂ :=
  (1 - etaJ : ℝ) + I * gamma

/-- The literal factor `f_j(t)` in Pintz equation (4.7), written before the
purely notational replacement `Y = exp λ`. -/
noncomputable def pintzF
    (Delta eta etaJ gamma lambda t : ℝ) : ℂ :=
  let s : ℂ := (pintzLeftEdge Delta eta etaJ : ℝ) + I * t
  riemannZeta ((1 - pintzXi Delta eta : ℝ) + I * (gamma + t)) /
      s * pintzGaussianNumerator lambda s

theorem pintz_rho_add_leftLine
    (Delta eta etaJ gamma t : ℝ) :
    pintzRho etaJ gamma +
        ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) =
      (1 - pintzXi Delta eta : ℝ) + I * (gamma + t) := by
  apply Complex.ext
  · simp [pintzRho, pintzLeftEdge, pintzDeltaJ, pintzXi]
    ring
  · simp [pintzRho, pintzLeftEdge, pintzDeltaJ, pintzXi]

/-- Pointwise source form of (4.7): the finite contour is the genuine finite
Möbius polynomial times the literal `f_j(t)`.  The source condition
`δ_j ≥ 0` is explicit. -/
theorem pintzFiniteContourIntegrand_left_eq_polynomial_mul_f_source
    {Delta eta etaJ gamma lambda t : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ) :
    pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda
        ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) =
      pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
          ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
        pintzF Delta eta etaJ gamma lambda t := by
  have hs : ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [pintzLeftEdge] at hre
    linarith
  rw [pintzFiniteContourIntegrand_eq_div hrhoZero hs]
  unfold pintzFiniteContourNumerator pintzF
  rw [pintz_rho_add_leftLine]
  ring

/-- The literal truncated left-line integral appearing in Pintz (4.6). -/
noncomputable def pintzEquation46Integral
    (Delta eta etaJ gamma lambda : ℝ) : ℂ :=
  VIntegral' (pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda)
    (pintzLeftEdge Delta eta etaJ) (-2 * lambda) (2 * lambda)

/-- The same integral with Pintz's equation-(4.7) factor exposed. -/
theorem pintzEquation46Integral_eq_source
    {Delta eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ) :
    pintzEquation46Integral Delta eta etaJ gamma lambda =
      (1 / (2 * Real.pi * I) : ℂ) * I *
        (∫ t in (-2 * lambda)..(2 * lambda),
          pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
              ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
            pintzF Delta eta etaJ gamma lambda t) := by
  unfold pintzEquation46Integral VIntegral' VIntegral
  simp only [smul_eq_mul]
  have hint :
      (∫ t in (-2 * lambda)..(2 * lambda),
        pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda
          ((pintzLeftEdge Delta eta etaJ : ℝ) + (t : ℂ) * I)) =
      (∫ t in (-2 * lambda)..(2 * lambda),
        pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
            ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) *
          pintzF Delta eta etaJ gamma lambda t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simpa [mul_comm] using
      (pintzFiniteContourIntegrand_left_eq_polynomial_mul_f_source
        hrhoZero hDelta hdeltaJ)
  rw [hint]
  ring

/-- All pieces suppressed by the `O`-notation in (4.6), retained as a
literal complex remainder. -/
noncomputable def pintzEquation46ContourError
    (Delta eta etaJ gamma lambda : ℝ) : ℂ :=
  let f := pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda
  (pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda -
      VIntegral' f 3 (-2 * lambda) (2 * lambda)) -
    HIntegral' f (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda) +
    HIntegral' f (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda)

/-- Exact, assumption-free error ledger behind Pintz equation (4.6).  The
only geometric restriction is that the translated zeta pole lies above the
height-`2λ` contour. -/
theorem pintz_equation_4_6_exact
    {Delta eta etaJ gamma lambda : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hrhoHalf : 1 / 2 <= (pintzRho etaJ gamma).re)
    (hlambda : 0 < lambda) (hDelta : 0 < Delta)
    (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hheight : 2 * lambda < |gamma|) :
    pintzMobiusFiniteHead (pintzRho etaJ gamma) lambda =
      pintzEquation46Integral Delta eta etaJ gamma lambda +
        pintzEquation46ContourError Delta eta etaJ gamma lambda := by
  let f := pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda
  have hleft : pintzLeftEdge Delta eta etaJ <= 3 := by
    unfold pintzLeftEdge
    linarith
  have him : (pintzRho etaJ gamma).im = gamma := by
    simp [pintzRho]
  have hshift := pintzFiniteContour_finite_vertical_shift
    (rho := pintzRho etaJ gamma) (lambda := lambda)
    (left := pintzLeftEdge Delta eta etaJ) (R := 2 * lambda)
    hleft (by linarith) (by simpa [him] using hheight)
  have hshift' :
      VIntegral' (pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda)
          (pintzLeftEdge Delta eta etaJ) (-2 * lambda) (2 * lambda) =
        VIntegral' (pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda)
            3 (-2 * lambda) (2 * lambda) +
          HIntegral' (pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda)
              (pintzLeftEdge Delta eta etaJ) 3 (-2 * lambda) -
            HIntegral' (pintzFiniteContourIntegrand (pintzRho etaJ gamma) lambda)
              (pintzLeftEdge Delta eta etaJ) 3 (2 * lambda) := by
    simpa only [neg_mul] using hshift
  have hhead := pintzFiniteContour_verticalIntegral_three_eq_head
    hrhoZero hrhoHalf hlambda
  unfold pintzEquation46Integral pintzEquation46ContourError
  dsimp only [f]
  rw [← hhead]
  linear_combination -hshift'

#print axioms pintz_rho_add_leftLine
#print axioms pintzFiniteContourIntegrand_left_eq_polynomial_mul_f_source
#print axioms pintzEquation46Integral_eq_source
#print axioms pintz_equation_4_6_exact

end

end GafniTao
