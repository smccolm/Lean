import TaoTrudgianYang2025.ZetaSquareDivisorKernel

/-!
# Complete ordinary-divisor series for the one-sided square

Each term is integrated over the entire right line. Absolute integrated
norm summability justifies Tonelli, and the actual contour limit identifies
the sum with the completed zeta square. No mean-square or moment theorem
is a hypothesis of this entry identity.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaSquareDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint t + (1 + (u : ℂ) * I)) n *
    zetaSquareRightKernel t u

theorem norm_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) (u : ℝ) :
    ‖zetaSquareDivisorTerm t n u‖ =
      ‖divisorDirichletTerm (3 / 2) n‖ * ‖zetaSquareRightKernel t u‖ := by
  simp only [zetaSquareDivisorTerm, norm_mul, divisorDirichletTerm, LSeries.norm_term_eq]
  norm_num [afeCriticalPoint]

theorem integrable_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) :
    Integrable (zetaSquareDivisorTerm t n) := by
  unfold zetaSquareDivisorTerm
  apply (integrable_zetaSquareRightKernel t).bdd_mul
    (c := ‖divisorDirichletTerm (3 / 2) n‖)
  · simpa using (continuous_divisorDirichletTerm_vertical t 1 n).aestronglyMeasurable
  · filter_upwards with u
    simp only [divisorDirichletTerm, LSeries.norm_term_eq]
    norm_num [afeCriticalPoint]

theorem integral_norm_zetaSquareDivisorTerm (t : ℝ) (n : ℕ) :
    (∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) =
      ‖divisorDirichletTerm (3 / 2) n‖ * ∫ u : ℝ, ‖zetaSquareRightKernel t u‖ := by
  simp_rw [norm_zetaSquareDivisorTerm]
  exact integral_const_mul _ _

theorem summable_integral_norm_zetaSquareDivisorTerm (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖zetaSquareDivisorTerm t n u‖) := by
  simp_rw [integral_norm_zetaSquareDivisorTerm]
  exact (summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm.mul_right _

theorem tsum_zetaSquareDivisorTerm (t u : ℝ) :
    (∑' n : ℕ, zetaSquareDivisorTerm t n u) =
      zetaSquareContourIntegrand t (1 + (u : ℂ) * I) := by
  simp only [zetaSquareDivisorTerm, tsum_mul_right, tsum_divisorDirichletTerm]
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor, mul_comm]

theorem integrable_zetaSquareContour_right (t : ℝ) :
    Integrable (fun u : ℝ => zetaSquareContourIntegrand t (1 + (u : ℂ) * I)) := by
  have hw : Continuous (fun u : ℝ => (1 : ℂ) + (u : ℂ) * I) := by fun_prop
  have hwne : ∀ u : ℝ, (1 : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    norm_num at this
  have hcont : Continuous (fun u : ℝ => zetaSquareContourIntegrand t (1 + (u : ℂ) * I)) :=
    ((differentiable_zetaSquareContourNumerator t).continuous.comp hw).div₀ hw hwne
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (3 / 2) n‖
  apply ((integrable_zetaSquareRightKernel t).norm.const_mul S).mono' hcont.aestronglyMeasurable
  filter_upwards with u
  rw [← tsum_zetaSquareDivisorTerm]
  have hsum : Summable (fun n : ℕ => ‖zetaSquareDivisorTerm t n u‖) := by
    simp_rw [norm_zetaSquareDivisorTerm]
    exact (summable_divisorDirichletTerm (s := (3 / 2 : ℂ)) (by norm_num)).norm.mul_right _
  calc
    ‖∑' n : ℕ, zetaSquareDivisorTerm t n u‖ ≤ ∑' n : ℕ, ‖zetaSquareDivisorTerm t n u‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = S * ‖zetaSquareRightKernel t u‖ := by
      simp_rw [norm_zetaSquareDivisorTerm, tsum_mul_right]
      rfl

def zetaSquareDivisorIntegral (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ u : ℝ, zetaSquareContourIntegrand t (1 + (u : ℂ) * I)

def zetaSquareDivisorContribution (t : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaSquareDivisorTerm t n u

/-- Tonelli on the complete line: the coefficientwise integrals form an
actual convergent series, not a prescribed value of an arbitrary sum. -/
theorem hasSum_zetaSquareDivisorContribution (t : ℝ) :
    HasSum (zetaSquareDivisorContribution t) (zetaSquareDivisorIntegral t) := by
  have h := hasSum_integral_of_summable_integral_norm
    (integrable_zetaSquareDivisorTerm t) (summable_integral_norm_zetaSquareDivisorTerm t)
  simp_rw [tsum_zetaSquareDivisorTerm] at h
  exact h.mul_left (1 / (2 * Real.pi) : ℂ)

theorem tendsto_zetaSquare_right_integral (t : ℝ) :
    Tendsto (fun H : ℝ => VIntegral' (zetaSquareContourIntegrand t) 1 (-H) H)
      atTop (𝓝 (zetaSquareDivisorIntegral t)) := by
  have h := (intervalIntegral_tendsto_integral (integrable_zetaSquareContour_right t)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (1 / (2 * Real.pi) : ℂ)
  convert h using 1
  funext H
  unfold VIntegral' VIntegral
  simp only [smul_eq_mul, Complex.ofReal_one]
  field_simp [Real.pi_ne_zero]
  rfl

/-- Exact two-piece divisor entry for the completed zeta square. The
horizontal remainders and both complete right contours have been justified. -/
theorem completedZeta_square_eq_divisor_integrals (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      zetaSquareDivisorIntegral t + zetaSquareDivisorIntegral (-t) := by
  exact tendsto_nhds_unique
    (zetaSquareAFE_vertical_limit_native t (c := 1) (by norm_num))
    ((tendsto_zetaSquare_right_integral t).add (tendsto_zetaSquare_right_integral (-t)))

theorem completedZeta_square_eq_divisor_series (t : ℝ) :
    completedRiemannZeta (afeCriticalPoint t) ^ 2 =
      (∑' n : ℕ, zetaSquareDivisorContribution t n) +
        ∑' n : ℕ, zetaSquareDivisorContribution (-t) n := by
  rw [(hasSum_zetaSquareDivisorContribution t).tsum_eq,
    (hasSum_zetaSquareDivisorContribution (-t)).tsum_eq]
  exact completedZeta_square_eq_divisor_integrals t

end TaoTrudgianYang2025
