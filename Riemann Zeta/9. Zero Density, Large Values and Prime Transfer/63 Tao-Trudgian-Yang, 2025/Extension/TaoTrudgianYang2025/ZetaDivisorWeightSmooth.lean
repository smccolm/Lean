import TaoTrudgianYang2025.ZetaDivisorWeightKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Smoothness of the actual divisor Mellin weight

Differentiation takes place in the complex logarithmic argument of the
literal contour integral. A locally uniform Gaussian majorant justifies
the differentiation; holomorphy then gives real smoothness of every order.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem hasDerivAt_zetaDivisorWeightKernel_complex (q : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun z : ℂ => zetaDivisorWeightKernel z w)
      (-zetaDivisorWeightNumerator q w) q := by
  have he := ((hasDerivAt_id q).neg.mul_const w).cexp
  have h := (he.const_mul (Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w)).div_const w
  convert h using 1
  unfold zetaDivisorWeightNumerator
  norm_num
  field_simp

theorem norm_zetaDivisorWeightNumerator_local_le (q₀ : ℂ) {q : ℂ}
    (hq : q ∈ Metric.ball q₀ 1) (u : ℝ) :
    ‖zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)‖ ≤
      (625 * Real.exp (100 + (|q₀.im| + 1) ^ 2 / 2)) *
        Real.exp (-q₀.re + 1) * zetaDivisorWeightEnvelope u := by
  have hdist : ‖q - q₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hq
  have hre : |q.re - q₀.re| < 1 := by
    exact (Complex.abs_re_le_norm (q - q₀)).trans_lt hdist
  have him : |q.im - q₀.im| < 1 := by
    exact (Complex.abs_im_le_norm (q - q₀)).trans_lt hdist
  have hqim : |q.im| ≤ |q₀.im| + 1 := by
    have h := abs_add_le (q.im - q₀.im) q₀.im
    simp only [sub_add_cancel] at h
    linarith
  apply (norm_zetaDivisorWeightNumerator_right_le (by positivity) hqim u).trans
  have henv : 0 ≤ zetaDivisorWeightEnvelope u := by unfold zetaDivisorWeightEnvelope; positivity
  gcongr
  linarith [(abs_lt.mp hre).1]

theorem hasDerivAt_zetaDivisorWeight (q : ℂ) :
    HasDerivAt zetaDivisorWeight
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, -zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)) q := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => -zetaDivisorWeightNumerator q (1 + (u : ℂ) * I)) :=
    (((differentiable_zetaDivisorWeightNumerator q).continuous.comp
      (by fun_prop : Continuous (fun u : ℝ => (1 : ℂ) + (u : ℂ) * I))).neg).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z : ℂ => fun u : ℝ => zetaDivisorWeightKernel z (1 + (u : ℂ) * I))
    (F' := fun z : ℂ => fun u : ℝ => -zetaDivisorWeightNumerator z (1 + (u : ℂ) * I))
    (Metric.ball_mem_nhds q (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun z => (continuous_zetaDivisorWeightKernel_right z).aestronglyMeasurable))
    (integrable_zetaDivisorWeightKernel_right q) hmeas
    (Filter.Eventually.of_forall (fun u z hz => by
      rw [norm_neg]
      exact norm_zetaDivisorWeightNumerator_local_le q hz u))
    (integrable_zetaDivisorWeightEnvelope.const_mul
      ((625 * Real.exp (100 + (|q.im| + 1) ^ 2 / 2)) * Real.exp (-q.re + 1)))
    (Filter.Eventually.of_forall (fun u z _ =>
      hasDerivAt_zetaDivisorWeightKernel_complex z (by
        intro he
        have := congrArg Complex.re he
        norm_num at this)))
  exact h.2.const_mul (1 / (2 * Real.pi) : ℂ)

theorem differentiable_zetaDivisorWeight : Differentiable ℂ zetaDivisorWeight :=
  fun q => (hasDerivAt_zetaDivisorWeight q).differentiableAt

theorem contDiff_zetaDivisorWeight_complex : ContDiff ℂ ∞ zetaDivisorWeight :=
  differentiable_zetaDivisorWeight.contDiff

theorem contDiff_zetaDivisorWeight : ContDiff ℝ ∞ zetaDivisorWeight :=
  contDiff_zetaDivisorWeight_complex.restrict_scalars ℝ

end TaoTrudgianYang2025
