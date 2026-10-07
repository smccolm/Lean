import GuthMaynard.HughesYoungPolygamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Direct integral comparison for the actual trigamma series -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- Nonnegative real shifts stay in the Gamma right half-plane. -/
theorem gamma_shift_ne_zero {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) : z + x ≠ 0 := by
  intro he
  have hh := congrArg Complex.re he
  simp only [add_re, ofReal_re, zero_re] at hh
  linarith

/-- The actual complex norm controls both the real shift and the imaginary height. -/
theorem gamma_shift_norm_lower {z : ℂ} (hz : 0 < z.re) (x : ℝ) :
    (x + |z.im|) / 2 ≤ ‖z + x‖ := by
  have hr := Complex.re_le_norm (z + x)
  have hi := Complex.abs_im_le_norm (z + x)
  simp only [add_re, ofReal_re] at hr
  simp only [add_im, ofReal_im, add_zero] at hi
  linarith

/-- The derivative of the genuine inverse-square integrand. -/
theorem hasDerivAt_gamma_shift_inv_sq {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => (z + t)⁻¹ ^ 2) (-2 * (z + x)⁻¹ ^ 3) x := by
  have hh := (((hasDerivAt_id (x : ℂ)).const_add z).inv (gamma_shift_ne_zero hz hx)).pow 2
  convert hh.comp_ofReal using 1
  dsimp
  field_simp

/-- A height-sensitive bound for the difference of the actual inverse squares on a real interval. -/
theorem norm_gamma_shift_inv_sq_sub_le {z : ℂ} (hz : 0 < z.re) (hy : 0 < |z.im|)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖(z + b)⁻¹ ^ 2 - (z + a)⁻¹ ^ 2‖ ≤ 16 * (b - a) / (a + |z.im|) ^ 3 := by
  have hbase : 0 < a + |z.im| := add_pos_of_nonneg_of_pos ha hy
  have hd (x : ℝ) (hx : x ∈ Icc a b) := hasDerivAt_gamma_shift_inv_sq hz (ha.trans hx.1)
  have hb (x : ℝ) (hx : x ∈ Icc a b) :
      ‖(-2 : ℂ) * (z + x)⁻¹ ^ 3‖ ≤ 16 / (a + |z.im|) ^ 3 := by
    have hl : (a + |z.im|) / 2 ≤ ‖z + x‖ :=
      (by linarith [hx.1] : (a + |z.im|) / 2 ≤ (x + |z.im|) / 2).trans
        (gamma_shift_norm_lower hz x)
    have hi : ‖z + x‖⁻¹ ≤ 2 / (a + |z.im|) := by
      simpa only [inv_div] using inv_anti₀ (half_pos hbase) hl
    rw [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow, norm_inv]
    calc
      _ ≤ 2 * (2 / (a + |z.im|)) ^ 3 := by gcongr
      _ = _ := by field_simp; ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (convex_Icc a b)
    (x := a) (y := b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  convert hh using 1
  ring

/-- The exact integral of the genuine inverse-square integrand on any nonnegative real interval. -/
theorem integral_gamma_shift_inv_sq {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, (z + x)⁻¹ ^ 2) = (z + a)⁻¹ - (z + b)⁻¹ := by
  have hc : ContinuousOn (fun x : ℝ => (z + x)⁻¹ ^ 2) (Icc a b) :=
    ((continuous_const.add Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => gamma_shift_ne_zero hz (ha.trans hx.1))).pow 2
  have hh : (∫ x in a..b, (z + x)⁻¹ ^ 2) = -(z + b)⁻¹ - (-(z + a)⁻¹) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ (hc.intervalIntegrable_of_Icc hab)
    intro x hx
    have hx0 : 0 ≤ x := ha.trans ((uIcc_of_le hab ▸ hx).1)
    have hd := (((hasDerivAt_id (x : ℂ)).const_add z).inv (gamma_shift_ne_zero hz hx0)).neg
    convert hd.comp_ofReal using 1
    dsimp
    field_simp
  rw [hh]
  ring

/-- A uniform unit-interval error for comparing the true trigamma series with its integral. -/
theorem norm_trigamma_integral_step_le {z : ℂ} (hz : 0 < z.re)
    (hy : 0 < |z.im|) (n : ℕ) :
    ‖(z + n)⁻¹ ^ 2 - ((z + n)⁻¹ - (z + (n + 1 : ℕ))⁻¹)‖ ≤
      16 / ((n : ℝ) + |z.im|) ^ 3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hint : IntervalIntegrable (fun x : ℝ => (z + x)⁻¹ ^ 2) volume n (n + 1) :=
    (((continuous_const.add Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => gamma_shift_ne_zero hz (hn.trans hx.1))).pow 2).intervalIntegrable_of_Icc (by linarith)
  have he : (z + n)⁻¹ ^ 2 - ((z + n)⁻¹ - (z + (n + 1 : ℕ))⁻¹) =
      ∫ x in (n : ℝ)..(n : ℝ) + 1, ((z + n)⁻¹ ^ 2 - (z + x)⁻¹ ^ 2) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      integral_gamma_shift_inv_sq hz hn (by linarith)]
    simp
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (n : ℝ)) (b := (n : ℝ) + 1)
    (f := fun x : ℝ => (z + n)⁻¹ ^ 2 - (z + x)⁻¹ ^ 2)
    (C := 16 / ((n : ℝ) + |z.im|) ^ 3) ?_
  · simpa using hh
  intro x hx
  rw [uIoc_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hx
  have hb := norm_gamma_shift_inv_sq_sub_le hz hy hn hx.1.le
  rw [norm_sub_rev] at hb
  simp only [Complex.ofReal_natCast] at hb
  refine hb.trans ?_
  have hnY : 0 < (n : ℝ) + |z.im| := add_pos_of_nonneg_of_pos hn hy
  apply (div_le_div_iff_of_pos_right (pow_pos hnY 3)).mpr
  linarith [hx.2]

end
end Dubon2026
