import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import RiemannZeta.External.PNT.ResidueCalcOnRectangles

/-!
# Pintz's Gaussian contour kernel

This is the literal exponential factor in Pintz, *On the density theorem of
Halász and Turán*, equations (4.1)--(4.8).  Keeping the numerator separate
from the simple factor `1 / s` makes both the residue at the origin and the
removable singularity after multiplication by a zero of zeta explicit.
-/

open Complex MeasureTheory

namespace GafniTao

noncomputable section

/-- The entire numerator `exp(s²/λ + λs)` in Pintz (4.1). -/
noncomputable def pintzGaussianNumerator (lambda : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s ^ 2 / (lambda : ℂ) + (lambda : ℂ) * s)

/-- The meromorphic Gaussian kernel `exp(s²/λ + λs) / s`. -/
noncomputable def pintzGaussianKernel (lambda : ℝ) (s : ℂ) : ℂ :=
  pintzGaussianNumerator lambda s / s

@[simp] theorem pintzGaussianNumerator_zero (lambda : ℝ) :
    pintzGaussianNumerator lambda 0 = 1 := by
  simp [pintzGaussianNumerator]

theorem analyticAt_pintzGaussianNumerator
    (lambda : ℝ) (s : ℂ) :
    AnalyticAt ℂ (pintzGaussianNumerator lambda) s := by
  unfold pintzGaussianNumerator
  fun_prop

theorem differentiableOn_pintzGaussianKernel_off_origin
    (lambda : ℝ) :
    DifferentiableOn ℂ (pintzGaussianKernel lambda) ({0}ᶜ : Set ℂ) := by
  intro s hs
  unfold pintzGaussianKernel
  exact ((analyticAt_pintzGaussianNumerator lambda s).differentiableAt.div
    differentiableAt_id (by simpa using hs)).differentiableWithinAt

/-- Exact Gaussian decay on a vertical line. -/
theorem norm_pintzGaussianNumerator_vertical
    (lambda c t : ℝ) (hlambda : 0 < lambda) :
    ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ =
      Real.exp ((c ^ 2 - t ^ 2) / lambda + lambda * c) := by
  rw [pintzGaussianNumerator, Complex.norm_exp]
  congr 1
  have hlambdaNe : lambda ≠ 0 := ne_of_gt hlambda
  rw [Complex.add_re, Complex.div_re]
  simp [Complex.normSq_apply, pow_two]
  field_simp

/-- The same formula factored into a constant line contribution and the
decaying Gaussian in the ordinate. -/
theorem norm_pintzGaussianNumerator_vertical_factored
    (lambda c t : ℝ) (hlambda : 0 < lambda) :
    ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ =
      Real.exp (c ^ 2 / lambda + lambda * c) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  rw [norm_pintzGaussianNumerator_vertical lambda c t hlambda]
  rw [← Real.exp_add]
  congr 1
  field_simp [ne_of_gt hlambda]
  ring

theorem integrable_norm_pintzGaussianNumerator_vertical
    (lambda c : ℝ) (hlambda : 0 < lambda) :
    Integrable
      (fun t : ℝ => ‖pintzGaussianNumerator lambda
        ((c : ℂ) + Complex.I * t)‖) := by
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)
  have hmul := hgaussian.const_mul
    (Real.exp (c ^ 2 / lambda + lambda * c))
  simpa only [norm_pintzGaussianNumerator_vertical_factored lambda c _ hlambda]
    using hmul

/-- On a vertical line separated from the origin, the complete Pintz kernel
is absolutely integrable. -/
theorem integrable_pintzGaussianKernel_vertical
    (lambda c : ℝ) (hlambda : 0 < lambda) (hc : c ≠ 0) :
    Integrable
      (fun t : ℝ => pintzGaussianKernel lambda
        ((c : ℂ) + Complex.I * t)) := by
  have hnum := integrable_norm_pintzGaussianNumerator_vertical lambda c hlambda
  have hmajor := hnum.const_mul (|c|⁻¹ + 1)
  apply Integrable.mono' hmajor
  · have hcont : Continuous
        (fun t : ℝ => pintzGaussianKernel lambda
          ((c : ℂ) + Complex.I * t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hline : ContinuousAt
          (fun u : ℝ => (c : ℂ) + Complex.I * u) t := by
        fun_prop
      change ContinuousAt
        (fun u : ℝ => pintzGaussianNumerator lambda
          ((c : ℂ) + Complex.I * u) /
            ((c : ℂ) + Complex.I * u)) t
      apply ContinuousAt.div
      · have hcomp : ContinuousAt
            ((pintzGaussianNumerator lambda) ∘
              (fun u : ℝ => (c : ℂ) + Complex.I * u)) t :=
          ContinuousAt.comp
            (f := fun u : ℝ => (c : ℂ) + Complex.I * u)
            (g := pintzGaussianNumerator lambda)
            (analyticAt_pintzGaussianNumerator lambda
              ((c : ℂ) + Complex.I * t)).continuousAt hline
        simpa only [Function.comp_apply] using hcomp
      · exact hline
      · intro heq
        have hre := congrArg Complex.re heq
        simp at hre
        exact hc hre
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with t
    rw [pintzGaussianKernel, norm_div]
    have hden : |c| ≤ ‖(c : ℂ) + Complex.I * t‖ := by
      simpa using Complex.abs_re_le_norm ((c : ℂ) + Complex.I * t)
    have hcabs : 0 < |c| := abs_pos.mpr hc
    have hdenPos : 0 < ‖(c : ℂ) + Complex.I * t‖ :=
      lt_of_lt_of_le hcabs hden
    have hinv : ‖(c : ℂ) + Complex.I * t‖⁻¹ ≤ |c|⁻¹ :=
      (inv_le_inv₀ hdenPos hcabs).2 hden
    calc
      ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ /
          ‖(c : ℂ) + Complex.I * t‖
          ≤ ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ /
              |c| := by
                simpa only [div_eq_mul_inv] using
                  mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ ≤ (|c|⁻¹ + 1) *
          ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ := by
            have hnorm : 0 ≤
                ‖pintzGaussianNumerator lambda ((c : ℂ) + Complex.I * t)‖ :=
              norm_nonneg _
            rw [div_eq_mul_inv]
            nlinarith [inv_nonneg.mpr hcabs.le]

#print axioms norm_pintzGaussianNumerator_vertical
#print axioms integrable_pintzGaussianKernel_vertical

end

end GafniTao
