import TaoTrudgianYang2025.ZetaGammaShiftAmplitude

/-!
# The actual pole-removing amplitude on a short complex shift

The normalization is the one used in the exact zeta-square source contour.
Its perturbation is bounded before it is multiplied by the actual Gamma
ratio. No pole factor is discarded in the leading-kernel approximation.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaSquarePoleShift (t : ℝ) (w : ℂ) : ℂ :=
  ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) ^ 2

theorem criticalPoint_pole_product (t : ℝ) :
    afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

theorem zetaSquarePoleShift_eq_source (t : ℝ) (w : ℂ) :
    zetaSquarePoleShift t w =
      ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w))) ^ 2 /
        zetaSquarePoleNormalization t := by
  rw [← zetaSquarePoleNormalization_neg]
  exact div_pow _ _ _

theorem poleShift_sub_one_identity (t : ℝ) (w : ℂ) :
    (afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1 =
      (2 * (t : ℂ) * I * w - w ^ 2) / ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  have hne : ((1 / 4 + t ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [criticalPoint_pole_product]
  rw [div_sub_one hne]
  congr 1
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

private theorem norm_poleShift_linear_sub_one_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) :
    ‖(afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1‖ ≤ 3 * ‖w‖ / t := by
  rw [poleShift_sub_one_identity, norm_div]
  have hn : ‖2 * (t : ℂ) * I * w - w ^ 2‖ ≤ 2 * t * ‖w‖ + ‖w‖ ^ 2 := by
    simpa only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] using
      norm_sub_le (2 * (t : ℂ) * I * w) (w ^ (2 : ℕ))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / 4 + t ^ 2)]
  apply (div_le_div_of_nonneg_right hn (by positivity)).trans
  apply (div_le_div_iff₀ (by positivity) ht).mpr
  have hwt : ‖w‖ * t ≤ t ^ 2 / 2 := by nlinarith
  nlinarith [norm_nonneg w,
    mul_nonneg (norm_nonneg w) (show 0 ≤ t ^ 2 - ‖w‖ * t by nlinarith)]

theorem norm_zetaSquarePoleShift_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) : ‖zetaSquarePoleShift t w‖ ≤ 9 := by
  have h := norm_poleShift_linear_sub_one_le ht hw
  have hfrac : 3 * ‖w‖ / t ≤ 3 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hn := norm_le_norm_sub_add
    ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) (1 : ℂ)
  simp only [norm_one] at hn
  rw [zetaSquarePoleShift, norm_pow]
  nlinarith [norm_nonneg ((afeCriticalPoint (-t) + w) *
    (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))))]

theorem norm_zetaSquarePoleShift_sub_one_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) : ‖zetaSquarePoleShift t w - 1‖ ≤ 12 * ‖w‖ / t := by
  let p := (afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))
  have h : ‖p - 1‖ ≤ 3 * ‖w‖ / t := norm_poleShift_linear_sub_one_le ht hw
  have hfrac : 3 * ‖w‖ / t ≤ 3 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hp : ‖p‖ ≤ 5 / 2 := by
    have hn := norm_le_norm_sub_add p (1 : ℂ)
    simp only [norm_one] at hn
    linarith
  have hpadd : ‖p + 1‖ ≤ 4 := by
    have hn := norm_add_le p (1 : ℂ)
    simp only [norm_one] at hn
    linarith
  change ‖p ^ 2 - 1‖ ≤ _
  rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by ring, norm_mul]
  calc
    _ ≤ (3 * ‖w‖ / t) * 4 := mul_le_mul h hpadd (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Uniform error for the product of the actual pole factor and the
actual squared Gamma quotient, with both errors retained. -/
theorem norm_poleShift_gammaReal_sq_sub_exp_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2) :
    ‖zetaSquarePoleShift t w * (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
        Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2 - Complex.exp (w * zetaGammaLeadingLog t)‖ ≤
      (9 * zetaGammaShiftError t w + 12 * ‖w‖ / t) *
        Real.exp (zetaGammaShiftError t w) * Real.exp ((w * zetaGammaLeadingLog t).re) := by
  let R := (Complex.Gammaℝ (afeCriticalPoint (-t) + w) /
    Complex.Gammaℝ (afeCriticalPoint (-t))) ^ 2
  let E := Complex.exp (w * zetaGammaLeadingLog t)
  have heq : zetaSquarePoleShift t w * R - E =
      zetaSquarePoleShift t w * (R - E) + (zetaSquarePoleShift t w - 1) * E := by ring
  change ‖zetaSquarePoleShift t w * R - E‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hB : 0 ≤ zetaGammaShiftError t w := zetaGammaShiftError_nonneg (by linarith) w
  have hexp : 1 ≤ Real.exp (zetaGammaShiftError t w) := Real.one_le_exp hB
  have hnE : ‖E‖ = Real.exp ((w * zetaGammaLeadingLog t).re) := Complex.norm_exp _
  rw [hnE]
  calc
    _ ≤ 9 * (zetaGammaShiftError t w * Real.exp (zetaGammaShiftError t w) *
        Real.exp ((w * zetaGammaLeadingLog t).re)) +
        (12 * ‖w‖ / t) * Real.exp ((w * zetaGammaLeadingLog t).re) := by
      gcongr
      · exact norm_zetaSquarePoleShift_le (by linarith) hw
      · exact norm_gammaReal_shift_sq_sub_exp_le ht hwre hw
      · exact norm_zetaSquarePoleShift_sub_one_le (by linarith) hw
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ (12 * ‖w‖ / t) * Real.exp ((w * zetaGammaLeadingLog t).re) by positivity)
      nlinarith

end TaoTrudgianYang2025
