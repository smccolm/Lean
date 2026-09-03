import GafniTao.PintzCorrectedPhysicalDensity

/-!
# Uniform form of Pintz's finite-contour error

The right vertical edge contains a finite Möbius coefficient mass depending
on the detected zero.  Absolute convergence in `Re s ≥ 3/2` removes that
dependence without introducing a new hypothesis.  The two horizontal edges
are then combined into one explicit error function.
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The finite coefficient mass on the right edge is bounded by the same
absolute Dirichlet-series constant used for zeta in `Re s ≥ 3/2`. -/
theorem pintzRightCoefficientMass_le_halfPlaneMajorant
    {rho : ℂ} {lambda : ℝ} (hrhoHalf : 1 / 2 ≤ rho.re) :
    pintzRightCoefficientMass rho lambda ≤
      hughesYoungZetaHalfPlaneMajorant := by
  unfold pintzRightCoefficientMass hughesYoungZetaHalfPlaneMajorant
  calc
    ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        ‖LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
          (((3 + rho.re : ℝ) : ℂ)) n‖ ≤
      ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
        ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
            (((3 + rho.re : ℝ) : ℂ)) n‖ ≤
          ‖LSeries.term (1 : ℕ → ℂ) (((3 + rho.re : ℝ) : ℂ)) n‖ :=
            LSeries.norm_term_le _ (moebius_coeff_norm_le_one n)
        _ ≤ ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ :=
          LSeries.norm_term_le_of_re_le_re (1 : ℕ → ℂ) (by
            norm_num
            linarith) n
    _ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (3 / 2 : ℂ) n‖ :=
      summable_hughesYoungZetaHalfPlaneMajorant.sum_le_tsum _
        (fun n hn => norm_nonneg _)

/-- Zero-independent bound for the deleted tails of the right edge. -/
noncomputable def pintzUniformRightTailBound (lambda : ℝ) : ℝ :=
  hughesYoungZetaHalfPlaneMajorant ^ 2 *
    ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
    (Real.exp (-(7 / 2 : ℝ) * lambda) *
      Real.sqrt (Real.pi / (1 / (8 * lambda))))

/-- Complete zero-independent contour-error envelope. -/
noncomputable def pintzUniformEquation46ErrorBound
    (lambda Z : ℝ) : ℝ :=
  pintzUniformRightTailBound lambda +
    2 * pintzEquation46HorizontalBound lambda Z

theorem pintzUniformRightTailBound_nonneg
    {lambda : ℝ} (hlambda : 0 < lambda) :
    0 ≤ pintzUniformRightTailBound lambda := by
  unfold pintzUniformRightTailBound
  positivity

theorem pintzEquation46RightTailBound_le_uniform
    {etaJ gamma lambda : ℝ}
    (hrhoHalf : 1 / 2 ≤ (pintzRho etaJ gamma).re)
    (hlambda : 0 < lambda) :
    pintzEquation46RightTailBound etaJ gamma lambda ≤
      pintzUniformRightTailBound lambda := by
  have hmass := pintzRightCoefficientMass_le_halfPlaneMajorant
    (lambda := lambda) hrhoHalf
  have hH : 0 ≤ hughesYoungZetaHalfPlaneMajorant :=
    hughesYoungZetaHalfPlaneMajorant_nonneg
  have hrest :
      0 ≤ ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by positivity
  unfold pintzEquation46RightTailBound pintzUniformRightTailBound
  calc
    pintzRightCoefficientMass (pintzRho etaJ gamma) lambda *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) ≤
      hughesYoungZetaHalfPlaneMajorant *
        hughesYoungZetaHalfPlaneMajorant *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by
      have hmul := mul_le_mul_of_nonneg_right hmass hH
      nlinarith [mul_le_mul_of_nonneg_right hmul hrest]
    _ = hughesYoungZetaHalfPlaneMajorant ^ 2 *
        ((1 / 3 : ℝ) * Real.exp (9 / lambda + 3 * lambda)) *
        (Real.exp (-(7 / 2 : ℝ) * lambda) *
          Real.sqrt (Real.pi / (1 / (8 * lambda)))) := by ring

/-- The exact equation-(4.6) error is bounded by the uniform envelope once
the detected zero lies in the critical strip. -/
theorem pintzEquation46ErrorBound_le_uniform
    {etaJ gamma lambda Z : ℝ}
    (hrhoHalf : 1 / 2 ≤ (pintzRho etaJ gamma).re)
    (hlambda : 0 < lambda) :
    pintzEquation46ErrorBound etaJ gamma lambda Z Z ≤
      pintzUniformEquation46ErrorBound lambda Z := by
  have hright := pintzEquation46RightTailBound_le_uniform
    hrhoHalf hlambda
  unfold pintzEquation46ErrorBound pintzUniformEquation46ErrorBound
  linarith

#print axioms pintzRightCoefficientMass_le_halfPlaneMajorant
#print axioms pintzEquation46RightTailBound_le_uniform
#print axioms pintzEquation46ErrorBound_le_uniform

end

end GafniTao
