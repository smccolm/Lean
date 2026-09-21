import TaoTrudgianYang2025.ZetaFourthSource
import TaoTrudgianYang2025.ZetaFourthGaussian
import TaoTrudgianYang2025.ZetaSquarePoleShift

/-!
# The normalized one-sided fourth-moment kernel

The contour parameter is a genuine complex shift. At real part one the
kernel is exactly the installed, absolutely convergent divisor contour.
Its norm exposes the actual squared Gamma quotient and pole factor.
-/

noncomputable section

open Complex MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaFourthKernel (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100*w^2) * hughesYoungAuxiliaryZero w *
    zetaSquarePoleShift t w *
      (Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t) / w

theorem zetaFourthKernel_one (t u : ℝ) :
    zetaFourthKernel t (1+(u:ℂ)*I) =
      zetaSquareRightKernel (-t) u / zetaSquareGammaNormalization t := by
  unfold zetaFourthKernel
  rw [zetaSquarePoleShift_eq_source]
  unfold zetaSquareRightKernel
  dsimp only
  rw [zetaSquarePoleNormalization_neg]
  simp only [div_eq_mul_inv]
  ring

theorem continuous_zetaFourthKernel_vertical (t : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)) := by
  have hgamma := continuous_GammaR_afe_vertical (-t) (c := c) (by linarith)
  have haux := differentiable_hughesYoungAuxiliaryZero.continuous
  have hw : ∀ u : ℝ, (c:ℂ)+(u:ℂ)*I ≠ 0 := by
    intro u hu
    have he := congrArg Complex.re hu
    norm_num at he
    linarith
  unfold zetaFourthKernel zetaSquarePoleShift
  apply Continuous.div ?_ (by fun_prop) hw
  fun_prop (disch := assumption)

theorem norm_zetaFourthKernel_vertical (t c u : ℝ) :
    ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ =
      Real.exp (100*c^2-100*u^2) *
        ‖hughesYoungAuxiliaryZero ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) /
          Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ /
        ‖(c:ℂ)+(u:ℂ)*I‖ := by
  have he : (100*((c:ℂ)+(u:ℂ)*I)^2).re = 100*c^2-100*u^2 := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  unfold zetaFourthKernel
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_exp, he,
    norm_gammaSquare_div_zetaSquareGammaNormalization]

theorem zetaFourthRightPiece_eq_divisor_integral (t : ℝ) :
    zetaFourthRightPiece t = (1/(2*Real.pi):ℂ) *
      ∫ u : ℝ, zetaFourthKernel t (1+(u:ℂ)*I) *
        LSeries (fun n : ℕ => (n.divisors.card:ℂ))
          (afeCriticalPoint (-t)+(1+(u:ℂ)*I)) := by
  unfold zetaFourthRightPiece zetaSquareDivisorIntegral
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [zetaSquareContourIntegrand_eq_rightKernel_mul_divisor, zetaFourthKernel_one]
  ring

theorem norm_gammaReal_shift_sq_le_exp {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t/2) :
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
      Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w*zetaGammaLeadingLog t).re) := by
  have h := norm_zetaGammaShiftAmplitude_le ht hwre hw (v := 1)
    (by constructor <;> norm_num)
  have he : (Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2 =
      zetaGammaShiftAmplitude t w 1 * Complex.exp (w*zetaGammaLeadingLog t) := by
    simp only [zetaGammaShiftAmplitude, Complex.ofReal_one, one_mul,
      neg_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, mul_one]
  rw [he, norm_mul, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using h) (by positivity)

end TaoTrudgianYang2025
