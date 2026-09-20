import TaoTrudgianYang2025.ZetaSquareGammaPhase

/-!
# Uniform logarithmic control along the actual shifted-Gamma path

The negative-height logarithm is kept on its principal branch. The
comparison below has explicit constants and precedes any Gamma-ratio
approximation; no asymptotic Gamma formula is an input.
-/

noncomputable section

open Complex Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

/-- The principal logarithm is uniformly Lipschitz in a lower half-plane
separated from its branch cut by the positive vertical distance `Y`. -/
theorem norm_log_sub_le_of_im_le_neg {a b : ℂ} {Y : ℝ} (hY : 0 < Y)
    (ha : a.im ≤ -Y) (hb : b.im ≤ -Y) :
    ‖Complex.log b - Complex.log a‖ ≤ ‖b - a‖ / Y := by
  let p : ℝ → ℂ := fun v => a + (v : ℂ) * (b - a)
  have him (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : (p v).im ≤ -Y := by
    dsimp [p]
    simp only [mul_im, ofReal_re, ofReal_im, sub_im, zero_mul, add_zero]
    have hv1 : 0 ≤ 1 - v := by linarith [hv.2]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hv.1 (sub_nonpos.mpr hb),
      mul_nonpos_of_nonneg_of_nonpos hv1 (sub_nonpos.mpr ha)]
  have hd (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => Complex.log (p u)) ((p v)⁻¹ * (b - a)) v := by
    have hslit : p v ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_lt (lt_of_le_of_lt (him v hv) (by linarith))))
    have hp : HasDerivAt (fun z : ℂ => a + z * (b - a)) (b - a) (v : ℂ) := by
      simpa using ((hasDerivAt_id (v : ℂ)).mul_const (b - a)).const_add a
    exact ((Complex.hasDerivAt_log hslit).comp (v : ℂ) hp).comp_ofReal
  have hbound (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖(p v)⁻¹ * (b - a)‖ ≤ ‖b - a‖ / Y := by
    have hnorm : Y ≤ ‖p v‖ := by
      have hn := Complex.abs_im_le_norm (p v)
      have hi := him v hv
      rw [abs_of_nonpos (by linarith : (p v).im ≤ 0)] at hn
      linarith
    rw [norm_mul, norm_inv, div_eq_mul_inv, mul_comm ‖b - a‖]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hY hnorm) (norm_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hd v hv).hasDerivWithinAt) hbound (convex_Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (by constructor <;> norm_num) (by constructor <;> norm_num)
  simpa [p] using h

def zetaGammaLeadingLog (t : ℝ) : ℂ :=
  (Real.log (t / (2 * Real.pi)) : ℂ) - ((Real.pi / 2 : ℝ) : ℂ) * I

def zetaGammaHalfShift (t : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  (afeCriticalPoint (-t) + (v : ℂ) * w) / 2

theorem zetaGammaHalfShift_re_pos (t : ℝ) {w : ℂ} (hw : 0 ≤ w.re)
    {v : ℝ} (hv : 0 ≤ v) : 0 < (zetaGammaHalfShift t w v).re := by
  simp only [zetaGammaHalfShift, Complex.div_ofNat_re, add_re, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero]
  norm_num [afeCriticalPoint]
  positivity

theorem zetaGammaHalfShift_im_le {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : ‖w‖ ≤ t / 2)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : (zetaGammaHalfShift t w v).im ≤ -t / 4 := by
  have hwi : w.im ≤ t / 2 := (Complex.im_le_norm w).trans hw
  have hvwi : v * w.im ≤ t / 2 := by
    have h := mul_le_mul_of_nonneg_left hwi hv.1
    nlinarith [hv.2]
  simp [zetaGammaHalfShift, afeCriticalPoint, Complex.mul_im]
  linarith

theorem log_negative_height_eq {t : ℝ} (ht : 0 < t) :
    Complex.log (-((t / 2 : ℝ) : ℂ) * I) =
      zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ) := by
  rw [show -((t / 2 : ℝ) : ℂ) * I = ((t / 2 : ℝ) : ℂ) * (-I) by ring,
    Complex.log_ofReal_mul (div_pos ht two_pos) (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I]
  unfold zetaGammaLeadingLog
  rw [Real.log_div ht.ne' (mul_ne_zero two_ne_zero Real.pi_ne_zero),
    Real.log_mul two_ne_zero Real.pi_ne_zero,
    Real.log_div ht.ne' two_ne_zero, ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  ring

theorem norm_zetaGammaHalfShift_sub_negative_height_le (t : ℝ) (w : ℂ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖zetaGammaHalfShift t w v - (-((t / 2 : ℝ) : ℂ) * I)‖ ≤ 1 / 4 + ‖w‖ / 2 := by
  have heq : zetaGammaHalfShift t w v - (-((t / 2 : ℝ) : ℂ) * I) =
      (1 / 4 : ℂ) + (v : ℂ) * w / 2 := by
    unfold zetaGammaHalfShift afeCriticalPoint
    push_cast
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_div, norm_mul, norm_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
  nlinarith [norm_nonneg w, hv.2]

/-- The actual digamma argument along the shift path is within an explicit
inverse-height error of the negative-height leading logarithm. -/
theorem norm_zetaGammaHalfShift_digamma_sub_le {t : ℝ} (ht : 4 ≤ t)
    {w : ℂ} (hwre : 0 ≤ w.re) (hw : ‖w‖ ≤ t / 2)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ‖Complex.digamma (zetaGammaHalfShift t w v) -
      (zetaGammaLeadingLog t + Complex.log (Real.pi : ℂ))‖ ≤ (17 + 2 * ‖w‖) / t := by
  have ht0 : 0 < t := by linarith
  have him := zetaGammaHalfShift_im_le ht0 hw hv
  have himabs : t / 4 ≤ |(zetaGammaHalfShift t w v).im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hd := norm_digamma_sub_log_le (zetaGammaHalfShift_re_pos t hwre hv.1)
    (show 1 ≤ |(zetaGammaHalfShift t w v).im| by linarith)
  have hl := norm_log_sub_le_of_im_le_neg (Y := t / 4) (a := -((t / 2 : ℝ) : ℂ) * I)
    (b := zetaGammaHalfShift t w v) (by positivity) (by simp; linarith)
    (by simpa only [neg_div] using him)
  have hd' : 4 / |(zetaGammaHalfShift t w v).im| ≤ 16 / t := by
    apply (div_le_div_iff₀ (by linarith) ht0).mpr
    linarith
  have hl' := div_le_div_of_nonneg_right (norm_zetaGammaHalfShift_sub_negative_height_le t w hv)
    (by positivity : 0 ≤ t / 4)
  rw [← log_negative_height_eq ht0]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (Complex.log (zetaGammaHalfShift t w v)) _).trans ?_
  calc
    _ ≤ 16 / t + (1 / 4 + ‖w‖ / 2) / (t / 4) := add_le_add (hd.trans hd') (hl.trans hl')
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
