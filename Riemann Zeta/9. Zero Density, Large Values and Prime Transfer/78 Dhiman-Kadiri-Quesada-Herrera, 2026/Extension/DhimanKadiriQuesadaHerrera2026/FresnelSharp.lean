import DhimanKadiriQuesadaHerrera2026.FresnelEvaluation
import Mathlib.Analysis.Complex.CauchyIntegral

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory Filter
open scoped Topology

/-- The exact Gaussian norm on a horizontal or vertical side of the upper rectangle. -/
theorem norm_fresnel_rectangle_kernel (ρ x y : ℝ) :
    ‖Complex.exp (Complex.I * (ρ : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ =
      Real.exp (-2 * ρ * x * y) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two]
  ring

/-- Each vertical side is bounded by the exact decaying exponential primitive. -/
theorem norm_fresnel_vertical_le {ρ a T : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hT : 0 ≤ T) :
    ‖∫ y in (0 : ℝ)..T,
      Complex.exp (Complex.I * (ρ : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ ≤
      1 / (2 * ρ * a) := by
  have hb : ‖∫ y in (0 : ℝ)..T,
      Complex.exp (Complex.I * (ρ : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ ≤
      ∫ y in (0 : ℝ)..T, Real.exp (-2 * ρ * a * y) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT
      (Eventually.of_forall (fun y _ => (norm_fresnel_rectangle_kernel ρ a y).le))
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-2 * ρ * a * y) / (-2 * ρ * a))
      (Real.exp (-2 * ρ * a * y)) y := by
    convert (((hasDerivAt_id y).const_mul (-2 * ρ * a)).exp).div_const (-2 * ρ * a) using 1
    simp only [id_eq]
    field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable (0 : ℝ) T)
  apply hb.trans
  rw [hi]
  simp only [mul_zero, Real.exp_zero]
  have hp : 0 < 2 * ρ * a := by positivity
  rw [show -2 * ρ * a = -(2 * ρ * a) by ring, div_neg, div_neg]
  have hn : 0 ≤ Real.exp (-(2 * ρ * a) * T) / (2 * ρ * a) := by positivity
  linarith

/-- The upper horizontal side decays uniformly while the real interval stays fixed. -/
theorem norm_fresnel_horizontal_le {ρ a b T : ℝ}
    (hρ : 0 < ρ) (hab : a ≤ b) (hT : 0 ≤ T) :
    ‖∫ x in a..b,
      Complex.exp (Complex.I * (ρ : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I) ^ 2)‖ ≤
      (b - a) * Real.exp (-2 * ρ * a * T) := by
  have hb : ‖∫ x in a..b,
      Complex.exp (Complex.I * (ρ : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I) ^ 2)‖ ≤
      ∫ _x in a..b, Real.exp (-2 * ρ * a * T) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall (fun x hx => ?_)) intervalIntegrable_const
    rw [norm_fresnel_rectangle_kernel]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * ρ * T) (sub_nonneg.mpr hx.1.le)]
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hb

/-- Cauchy's rectangle identity gives a finite quadratic-tail bound with both endpoint scales. -/
theorem norm_fresnel_finite_tail_sharp {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)‖ ≤
      1 / (2 * ρ * a) + 1 / (2 * ρ * b) := by
  have hb : 0 < b := ha.trans_le hab
  have hbound (T : ℝ) (hT : 0 ≤ T) :
      ‖∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)‖ ≤
        (b - a) * Real.exp (-2 * ρ * a * T) + 1 / (2 * ρ * a) + 1 / (2 * ρ * b) := by
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (fun z : ℂ => Complex.exp (Complex.I * (ρ : ℂ) * z ^ 2)) (a : ℂ)
      ((b : ℂ) + (T : ℂ) * Complex.I)
      (by fun_prop)
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      zero_add, Complex.ofReal_zero, zero_mul, add_zero, mul_one, smul_eq_mul] at hrect
    have he : (∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)) =
        (∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I) ^ 2)) +
        Complex.I * (∫ y in (0 : ℝ)..T, Complex.exp (Complex.I * (ρ : ℂ) * ((a : ℂ) + (y : ℂ) * Complex.I) ^ 2)) -
        Complex.I * (∫ y in (0 : ℝ)..T, Complex.exp (Complex.I * (ρ : ℂ) * ((b : ℂ) + (y : ℂ) * Complex.I) ^ 2)) := by
      linear_combination hrect
    rw [he]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul, Complex.norm_I, one_mul]
    exact add_le_add (add_le_add (norm_fresnel_horizontal_le hρ hab hT)
      (norm_fresnel_vertical_le hρ ha hT)) (norm_fresnel_vertical_le hρ hb hT)
  have ht : Tendsto (fun T : ℝ => (b - a) * Real.exp (-2 * ρ * a * T) +
      1 / (2 * ρ * a) + 1 / (2 * ρ * b)) atTop
      (𝓝 (1 / (2 * ρ * a) + 1 / (2 * ρ * b))) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * ρ * a))).const_mul (b - a)
    simpa only [neg_mul, mul_zero, zero_add] using
      (h.add_const (1 / (2 * ρ * a))).add_const (1 / (2 * ρ * b))
  exact ge_of_tendsto ht ((eventually_ge_atTop 0).mono fun T hT => hbound T hT)

/-- Conjugation transfers the sharp rectangle estimate to the negative quadratic phase. -/
theorem norm_fresnel_negative_finite_tail {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, Complex.exp (((-ρ * x ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      1 / (2 * ρ * a) + 1 / (2 * ρ * b) := by
  have he (x : ℝ) : Complex.exp (((-ρ * x ^ 2 : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow]
    ring
  simp_rw [he]
  have hi : (∫ x in a..b, (starRingEnd ℂ) (Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2))) =
      (starRingEnd ℂ) (∫ x in a..b, Complex.exp (Complex.I * (ρ : ℂ) * (x : ℂ) ^ 2)) := by
    simp only [intervalIntegral, integral_conj, map_sub]
  rw [hi, Complex.norm_conj]
  exact norm_fresnel_finite_tail_sharp hρ ha hab

/-- Evenness identifies the existing quadratic window with twice the positive half-window. -/
theorem quadraticWindow_eq_twice (c H : ℝ) :
    quadraticWindow c H = 2 * ∫ x in (0 : ℝ)..H,
      Complex.exp (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * Complex.I) := by
  simpa only [fresnelDampedKernel_zero, quadraticWindow] using
    integral_symmetric_fresnelDampedKernel 0 c H

/-- The difference of two actual symmetric windows has the sharp reciprocal-endpoint bound. -/
theorem norm_quadraticWindow_sub_window_sharp {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖quadraticWindow c b - quadraticWindow c a‖ ≤
      1 / (2 * Real.pi * c * a) + 1 / (2 * Real.pi * c * b) := by
  let K : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * Complex.I)
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) 0 a) (hK.intervalIntegrable a b)
  have he : quadraticWindow c b - quadraticWindow c a = 2 * ∫ x in a..b, K x := by
    rw [quadraticWindow_eq_twice, quadraticWindow_eq_twice]
    change 2 * (∫ x in (0 : ℝ)..b, K x) - 2 * (∫ x in (0 : ℝ)..a, K x) = _
    linear_combination -2 * hi
  rw [he, norm_mul, Complex.norm_ofNat]
  have h := norm_fresnel_negative_finite_tail (by positivity : 0 < 2 * Real.pi * c) ha hab
  have hn : (fun x : ℝ => Complex.exp (((-(2 * Real.pi * c) * x ^ 2 : ℝ) : ℂ) * Complex.I)) = K := by
    funext x
    dsimp [K]
    congr 3
    ring
  rw [hn] at h
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

/-- Passing to the already proved Fresnel limit yields the sharp symmetric quadratic tail. -/
theorem norm_quadraticWindow_sub_fresnel_sharp {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    ‖quadraticWindow c H -
      Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) / (Real.sqrt (2 * c) : ℂ)‖ ≤
      1 / (2 * Real.pi * c * H) := by
  rw [norm_sub_rev]
  have hl := ((tendsto_quadraticWindow hc).sub_const (quadraticWindow c H)).norm
  have hr : Tendsto (fun R : ℝ => 1 / (2 * Real.pi * c * H) + 1 / (2 * Real.pi * c * R))
      atTop (𝓝 (1 / (2 * Real.pi * c * H))) := by
    have ht := tendsto_inv_atTop_zero.const_mul (1 / (2 * Real.pi * c))
    convert ht.const_add (1 / (2 * Real.pi * c * H)) using 1
    · funext R
      ring
    · simp
  apply le_of_tendsto_of_tendsto hl hr
  exact (eventually_ge_atTop H).mono fun R hR => norm_quadraticWindow_sub_window_sharp hc hH hR

/-- Negative curvature has the source-normalized sharp tail, including the minus-one-eighth phase. -/
theorem quadratic_stationary_phase_sharp (A : ℝ) {κ H : ℝ} (hκ : κ < 0) (hH : 0 < H) :
    ‖(∫ v in (-H)..H,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A + κ * v ^ 2 / 2 : ℝ) : ℂ))) -
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ)‖ ≤ 1 / (Real.pi * |κ| * H) := by
  have hc : 0 < -κ / 2 := by linarith
  have he (v : ℝ) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A + κ * v ^ 2 / 2 : ℝ) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ)) *
        Complex.exp (((-2 * Real.pi * (-κ / 2) * v ^ 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hv : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ)) *
      (Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) / (Real.sqrt (2 * (-κ / 2)) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ) := by
    rw [← mul_div_assoc, ← Complex.exp_add,
      show 2 * (-κ / 2) = |κ| by rw [abs_of_neg hκ]; ring]
    congr 2
    push_cast
    ring
  have hn : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (A : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [← hv, ← mul_sub, norm_mul, hn, one_mul]
  apply (norm_quadraticWindow_sub_fresnel_sharp hc hH).trans_eq
  rw [abs_of_neg hκ]
  ring

end DhimanKadiriQuesadaHerrera2026


