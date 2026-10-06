import DhimanKadiriQuesadaHerrera2026.OscillatoryParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Cubic nonstationary error with bounded third derivative

These estimates use the actual integrals and their complex boundary terms.
No monotonicity of curvature quotients or continuity of the third derivative is assumed.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- Integration by parts needs integrable amplitude derivatives, without adding continuity of a third derivative. -/
theorem oscillatory_parts_integrable {a b : ℝ} {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.uIcc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.uIcc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.uIcc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.uIcc a b)) (hppi : IntervalIntegrable p' volume a b)
    (hhpi : IntervalIntegrable h' volume a b) (hn : ∀ u ∈ Set.uIcc a b, p u ≠ 0) :
    (∫ u in a..b, (h u : ℂ) * exp (I * (f u : ℂ))) =
      ((h b / p b : ℝ) * exp (I * (f b : ℂ)) -
        (h a / p a : ℝ) * exp (I * (f a : ℂ))) / I -
      (∫ u in a..b, (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ) *
        exp (I * (f u : ℂ))) / I := by
  have hhc : ContinuousOn h (Set.uIcc a b) := fun u hu => (hh u hu).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Set.uIcc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have he (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      HasDerivAt (fun v => exp (I * (f v : ℂ)))
        ((I * (p u : ℂ)) * exp (I * (f u : ℂ))) u := by
    convert (((hf u hu).ofReal_comp.const_mul I).cexp) using 1
    ring
  have hq (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      HasDerivAt (fun v => ((h v / p v : ℝ) : ℂ))
        (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ) u :=
    ((hh u hu).div (hp u hu) (hn u hu)).ofReal_comp
  have hqi : IntervalIntegrable (fun u => (h' u * p u - h u * p' u) / (p u) ^ 2) volume a b := by
    simp only [div_eq_mul_inv]
    exact ((hhpi.mul_continuousOn hpc).sub (hppi.continuousOn_mul hhc)).mul_continuousOn
      ((hpc.pow 2).inv₀ (fun u hu => pow_ne_zero _ (hn u hu)))
  have hqic : IntervalIntegrable (fun u => (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ)) volume a b := ⟨Complex.ofRealCLM.integrable_comp hqi.1, Complex.ofRealCLM.integrable_comp hqi.2⟩
  have hec : ContinuousOn (fun u => (I * (p u : ℂ)) * exp (I * (f u : ℂ)))
      (Set.uIcc a b) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq he
    hqic hec.intervalIntegrable
  have hi : (∫ u in a..b, ((h u / p u : ℝ) : ℂ) *
      ((I * (p u : ℂ)) * exp (I * (f u : ℂ)))) =
      I * (∫ u in a..b, (h u : ℂ) * exp (I * (f u : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    have hn' : (p u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hn u hu)
    push_cast
    field_simp
  rw [hi] at hparts
  rw [← sub_div]
  apply (eq_div_iff I_ne_zero).mpr
  linear_combination hparts

/-- A bounded ordinary derivative is Lebesgue integrable on every compact source interval. -/
theorem intervalIntegrable_deriv_bounded {f : ℝ → ℝ} {a b D : ℝ}
    (hD : ∀ u ∈ Set.uIcc a b, |deriv f u| ≤ D) :
    IntervalIntegrable (deriv f) volume a b := by
  apply (intervalIntegrable_const (c := D)).mono_fun' (aestronglyMeasurable_deriv f _)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  simpa only [Real.norm_eq_abs] using hD u (Set.uIoc_subset_uIcc hu)

/-- Two integrations by parts retain the actual curvature boundary and measurable third-derivative remainder. -/
theorem oscillatory_parts_twice {f p k : ℝ → ℝ} {a b D : ℝ}
    (hf : ∀ u ∈ Set.uIcc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.uIcc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.uIcc a b, DifferentiableAt ℝ k u)
    (hn : ∀ u ∈ Set.uIcc a b, p u ≠ 0)
    (hD : ∀ u ∈ Set.uIcc a b, |deriv k u| ≤ D) :
    (∫ u in a..b, exp (I * (f u : ℂ))) =
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I -
      (((k b / (p b) ^ 3 : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((k a / (p a) ^ 3 : ℝ) : ℂ) * exp (I * (f a : ℂ))) +
      ∫ u in a..b, (((deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 : ℝ) : ℂ)) *
        exp (I * (f u : ℂ)) := by
  have hpc : ContinuousOn p (Set.uIcc a b) := fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hkc : ContinuousOn k (Set.uIcc a b) := fun u hu => (hk u hu).continuousAt.continuousWithinAt
  have hki : IntervalIntegrable k volume a b := hkc.intervalIntegrable
  have hdi := intervalIntegrable_deriv_bounded hD
  let q := fun u => k u / (p u) ^ 2
  let q' := fun u => deriv k u / (p u) ^ 2 - 2 * (k u) ^ 2 / (p u) ^ 3
  have hq (u : ℝ) (hu : u ∈ Set.uIcc a b) : HasDerivAt q (q' u) u := by
    convert (hk u hu).hasDerivAt.div ((hp u hu).pow 2) (pow_ne_zero 2 (hn u hu)) using 1
    dsimp [q']
    field_simp
  have hq'i : IntervalIntegrable q' volume a b := by
    dsimp [q']
    have hi := hdi.mul_continuousOn ((hpc.pow 2).inv₀ (fun u hu => pow_ne_zero _ (hn u hu)))
    have hc : ContinuousOn (fun u => 2 * (k u) ^ 2 / (p u) ^ 3) (Set.uIcc a b) :=
      (continuousOn_const.mul (hkc.pow 2)).div (hpc.pow 3) (fun u hu => pow_ne_zero _ (hn u hu))
    simpa only [div_eq_mul_inv] using hi.sub hc.intervalIntegrable
  have hfirst := oscillatory_parts_integrable hf hp (fun u _ => hasDerivAt_const u (1 : ℝ)) hpc hki
    (intervalIntegrable_const (c := (0 : ℝ))) hn
  simp only [Complex.ofReal_one, one_mul, zero_mul, zero_sub, neg_div, Complex.ofReal_neg,
    neg_mul, intervalIntegral.integral_neg] at hfirst
  have hsecond := oscillatory_parts_integrable hf hp hq hpc hki hq'i hn
  have hquot (u : ℝ) : q u / p u = k u / (p u) ^ 3 := by dsimp [q]; ring
  have herror (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      (q' u * p u - q u * k u) / (p u) ^ 2 = deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 := by
    dsimp [q, q']
    have hpu := hn u hu
    field_simp
    ring
  have he : (∫ u in a..b, (((q' u * p u - q u * k u) / (p u) ^ 2 : ℝ) : ℂ) * exp (I * (f u : ℂ))) =
      ∫ u in a..b, (((deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 : ℝ) : ℂ)) * exp (I * (f u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [herror u hu]
  rw [hquot b, hquot a, he] at hsecond
  change (∫ u in a..b, exp (I * (f u : ℂ))) = _ - (-((∫ u in a..b, (q u : ℂ) * exp (I * (f u : ℂ))) / I)) at hfirst
  rw [hfirst, hsecond]
  simp only [div_eq_mul_inv, Complex.inv_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The curvature-square term integrates to endpoint reciprocals without any monotonicity condition on the curvature itself. -/
theorem curvature_square_integral {p k : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hkc : ContinuousOn k (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ) :
    (∫ u in a..b, 3 * (k u) ^ 2 / (p u) ^ 4) ≤ κ * (1 / (p b) ^ 3 - 1 / (p a) ^ 3) := by
  have hpc : ContinuousOn p (Set.Icc a b) := fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hn (u : ℝ) (hu : u ∈ Set.Icc a b) : p u ≠ 0 := (hpos u hu).ne'
  have hq (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun v => 1 / (p v) ^ 3) (-3 * k u / (p u) ^ 4) u := by
    convert (hasDerivAt_const u (1 : ℝ)).div ((hp u hu).pow 3) (pow_ne_zero 3 (hn u hu)) using 1
    have hpu := hn u hu
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hqc : ContinuousOn (fun u => -3 * k u / (p u) ^ 4) (Set.Icc a b) :=
    (continuousOn_const.mul hkc).div (hpc.pow 4) (fun u hu => pow_ne_zero _ (hn u hu))
  have hbc : ContinuousOn (fun u => 3 * (k u) ^ 2 / (p u) ^ 4) (Set.Icc a b) :=
    (continuousOn_const.mul (hkc.pow 2)).div (hpc.pow 4) (fun u hu => pow_ne_zero _ (hn u hu))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (hbc.intervalIntegrable_of_Icc hab) ((continuousOn_const.mul hqc).intervalIntegrable_of_Icc hab)
    (show ∀ u ∈ Set.Icc a b, 3 * (k u) ^ 2 / (p u) ^ 4 ≤ κ * (-3 * k u / (p u) ^ 4) from by
      intro u hu
      have hb := hkb u hu
      rw [abs_of_nonpos (hkneg u hu)] at hb
      have hm := mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr (hkneg u hu))
      have hh := div_le_div_of_nonneg_right (show 3 * (k u) ^ 2 ≤ κ * (-3 * k u) by nlinarith) (pow_nonneg (hpos u hu).le 4)
      simpa only [mul_div_assoc] using hh)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (Set.uIcc_of_le hab ▸ hq)
      (hqc.intervalIntegrable_of_Icc hab)] at hi
  exact hi

/-- The measurable third-derivative remainder has a uniform length term and an exact endpoint curvature term. -/
theorem norm_cubic_remainder {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hkc : ContinuousOn k (Set.Icc a b))
    (hmin : ∀ u ∈ Set.Icc a b, ρ ≤ p u)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖∫ u in a..b, (((deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 : ℝ) : ℂ)) *
      exp (I * (f u : ℂ))‖ ≤ D * (b - a) / ρ ^ 3 + κ * (1 / (p b) ^ 3 - 1 / (p a) ^ 3) := by
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < p u := hρ.trans_le (hmin u hu)
  have hpc : ContinuousOn p (Set.Icc a b) := fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hbc : ContinuousOn (fun u => 3 * (k u) ^ 2 / (p u) ^ 4) (Set.Icc a b) :=
    (continuousOn_const.mul (hkc.pow 2)).div (hpc.pow 4) (fun u hu => pow_ne_zero _ (hpos u hu).ne')
  have hi : ‖∫ u in a..b, (((deriv k u / (p u) ^ 3 - 3 * (k u) ^ 2 / (p u) ^ 4 : ℝ) : ℂ)) *
      exp (I * (f u : ℂ))‖ ≤ ∫ u in a..b, D / ρ ^ 3 + 3 * (k u) ^ 2 / (p u) ^ 4 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall (fun u hu => ?_))
      ((continuousOn_const.add hbc).intervalIntegrable_of_Icc hab)
    have hu' : u ∈ Set.Icc a b := ⟨hu.1.le, hu.2⟩
    have he : ‖exp (I * (f u : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hs := norm_sub_le (deriv k u / (p u) ^ 3) (3 * (k u) ^ 2 / (p u) ^ 4)
    simp only [Real.norm_eq_abs] at hs
    rw [abs_div, abs_of_pos (pow_pos (hpos u hu') 3),
      abs_of_nonneg (by positivity : 0 ≤ 3 * (k u) ^ 2 / (p u) ^ 4)] at hs
    have hh := div_le_div₀ ((abs_nonneg _).trans (hD u hu')) (hD u hu') (pow_pos hρ 3)
      (pow_le_pow_left₀ hρ.le (hmin u hu') 3)
    simp only [Pi.add_apply]
    linarith
  rw [intervalIntegral.integral_add intervalIntegrable_const (hbc.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hcurve := curvature_square_integral hab hp hkc hpos hkneg hkb
  have he : (b - a) * (D / ρ ^ 3) = D * (b - a) / ρ ^ 3 := by ring
  rw [he] at hi
  linarith only [hi, hcurve]

/-- A positive nonstationary phase has a second-order error requiring only bounded curvature and third derivative. -/
theorem norm_oscillatory_positive_cubic {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hmin : ∀ u ∈ Set.Icc a b, ρ ≤ p u)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I‖ ≤
      (2 * κ + D * (b - a)) / ρ ^ 3 := by
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < p u := hρ.trans_le (hmin u hu)
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (hkb a haa)
  have hkc : ContinuousOn k (Set.Icc a b) := fun u hu => (hk u hu).continuousAt.continuousWithinAt
  have hid := oscillatory_parts_twice (Set.uIcc_of_le hab ▸ hf) (Set.uIcc_of_le hab ▸ hp)
    (Set.uIcc_of_le hab ▸ hk) (Set.uIcc_of_le hab ▸ (fun u hu => (hpos u hu).ne')) (Set.uIcc_of_le hab ▸ hD)
  have hr := norm_cubic_remainder (f := f) hab hρ hp hkc hmin hkneg hkb hD
  have hbound (u : ℝ) (hu : u ∈ Set.Icc a b) :
      ‖((k u / (p u) ^ 3 : ℝ) : ℂ) * exp (I * (f u : ℂ))‖ ≤ κ / (p u) ^ 3 := by
    have he : ‖exp (I * (f u : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (hpos u hu) 3)]
    exact div_le_div_of_nonneg_right (hkb u hu) (pow_pos (hpos u hu) 3).le
  have hb := (norm_sub_le _ _).trans (add_le_add (hbound b hbb) (hbound a haa))
  rw [hid]
  rw [show ∀ B C R : ℂ, B - C + R - B = -C + R by intros; ring]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply (add_le_add hb hr).trans
  have hrec := div_le_div_of_nonneg_left hκ (pow_pos hρ 3) (pow_le_pow_left₀ hρ.le (hmin b hbb) 3)
  norm_num only [div_eq_mul_inv] at hrec ⊢
  nlinarith only [hrec]

/-- Reflection gives the same cubic remainder for a negative nonstationary derivative. -/
theorem norm_oscillatory_negative_cubic {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hmax : ∀ u ∈ Set.Icc a b, p u ≤ -ρ)
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (I * (f a : ℂ))) / I‖ ≤
      (2 * κ + D * (b - a)) / ρ ^ 3 := by
  have hmap {u : ℝ} (hu : u ∈ Set.Icc (-b) (-a)) : -u ∈ Set.Icc a b := by
    constructor <;> linarith [hu.1, hu.2]
  have hfd (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun v => f (-v)) (-p (-u)) u := by
    convert (hf (-u) (hmap hu)).comp u (hasDerivAt_neg u) using 1
    ring
  have hpd (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun v => -p (-v)) (k (-u)) u := by
    convert ((hp (-u) (hmap hu)).comp u (hasDerivAt_neg u)).neg using 1
    ring
  have hkd (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (fun v => k (-v)) (-deriv k (-u)) u := by
    convert (hk (-u) (hmap hu)).hasDerivAt.comp u (hasDerivAt_neg u) using 1
    ring
  have h := norm_oscillatory_positive_cubic (by linarith : -b ≤ -a) hρ hfd hpd
    (fun u hu => (hkd u hu).differentiableAt) (fun u hu => by linarith [hmax (-u) (hmap hu)])
    (fun u hu => hkneg (-u) (hmap hu)) (fun u hu => hkb (-u) (hmap hu))
    (fun u hu => by rw [(hkd u hu).deriv, abs_neg]; exact hD (-u) (hmap hu))
  rw [intervalIntegral.integral_comp_neg (fun u => exp (I * (f u : ℂ)))] at h
  simpa only [neg_neg, div_neg, Complex.ofReal_neg, neg_mul, neg_sub_neg] using h

set_option maxHeartbeats 800000 in
/-- The source 2π normalization gives a cubic Fourier error under ordinary third-derivative bounds. -/
theorem norm_expMode_cubic {f p k : ℝ → ℝ} {a b κ D ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (k u) u)
    (hk : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ k u)
    (hside : (∀ u ∈ Set.Icc a b, ρ ≤ p u) ∨ (∀ u ∈ Set.Icc a b, p u ≤ -ρ))
    (hkneg : ∀ u ∈ Set.Icc a b, k u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |k u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv k u| ≤ D) :
    ‖(∫ u in a..b, exp (2 * Real.pi * I * (f u : ℂ))) -
      (((1 / p b : ℝ) : ℂ) * exp (2 * Real.pi * I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (2 * Real.pi * I * (f a : ℂ))) / (2 * Real.pi * I)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ρ ^ 3) := by
  let A : ℝ := 2 * Real.pi
  have hA : 0 < A := Real.two_pi_pos
  have hfd (u : ℝ) (hu : u ∈ Set.Icc a b) : HasDerivAt (fun v => A * f v) (A * p u) u := (hf u hu).const_mul A
  have hpd (u : ℝ) (hu : u ∈ Set.Icc a b) : HasDerivAt (fun v => A * p v) (A * k u) u := (hp u hu).const_mul A
  have hkd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ (fun v => A * k v) u := (hk u hu).const_mul A
  have hkn (u : ℝ) (hu : u ∈ Set.Icc a b) : A * k u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le (hkneg u hu)
  have hkb' (u : ℝ) (hu : u ∈ Set.Icc a b) : |A * k u| ≤ A * κ := by
    rw [abs_mul, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left (hkb u hu) hA.le
  have hD' (u : ℝ) (hu : u ∈ Set.Icc a b) : |deriv (fun v => A * k v) u| ≤ A * D := by
    rw [((hk u hu).hasDerivAt.const_mul A).deriv, abs_mul, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left (hD u hu) hA.le
  have h : ‖(∫ u in a..b, exp (I * ((A * f u : ℝ) : ℂ))) -
      (((1 / (A * p b) : ℝ) : ℂ) * exp (I * ((A * f b : ℝ) : ℂ)) -
        ((1 / (A * p a) : ℝ) : ℂ) * exp (I * ((A * f a : ℝ) : ℂ))) / I‖ ≤
      (2 * (A * κ) + (A * D) * (b - a)) / (A * ρ) ^ 3 := by
    rcases hside with hmin | hmax
    · exact norm_oscillatory_positive_cubic (f := fun u => A * f u) (p := fun u => A * p u) (k := fun u => A * k u) (κ := A * κ) (D := A * D) (ρ := A * ρ) hab (mul_pos hA hρ) hfd hpd hkd
        (fun u hu => mul_le_mul_of_nonneg_left (hmin u hu) hA.le) hkn hkb' hD'
    · exact norm_oscillatory_negative_cubic (f := fun u => A * f u) (p := fun u => A * p u) (k := fun u => A * k u) (κ := A * κ) (D := A * D) (ρ := A * ρ) hab (mul_pos hA hρ) hfd hpd hkd
        (fun u hu => by nlinarith [mul_le_mul_of_nonneg_left (hmax u hu) hA.le]) hkn hkb' hD'
  have hex (u : ℝ) : I * ((A * f u : ℝ) : ℂ) = 2 * Real.pi * I * (f u : ℂ) := by dsimp [A]; push_cast; ring
  simp_rw [hex] at h
  have he : (((1 / (A * p b) : ℝ) : ℂ) * exp (2 * Real.pi * I * (f b : ℂ)) -
      ((1 / (A * p a) : ℝ) : ℂ) * exp (2 * Real.pi * I * (f a : ℂ))) / I =
      (((1 / p b : ℝ) : ℂ) * exp (2 * Real.pi * I * (f b : ℂ)) -
        ((1 / p a : ℝ) : ℂ) * exp (2 * Real.pi * I * (f a : ℂ))) / (2 * Real.pi * I) := by
    dsimp [A]
    push_cast
    ring
  rw [he] at h
  apply h.trans_eq
  dsimp [A]
  field_simp
  ring

end DhimanKadiriQuesadaHerrera2026
