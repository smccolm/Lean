import DongWangWangZhang2026.MeanValueTransform
import DongWangWangZhang2026.PowerSumEstimate
import GuthMaynard.ZetaBounds

/-!
# Convergent transform after subtracting the actual zeta pole term

The bounded power-sum remainder permits continuation into the strip without
discarding the explicit main term. That term is restored in the Gaussian identity.
-/

namespace DongWangWangZhang2026

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology

noncomputable section

/-- Actual power-sum remainder, cut off below one for its Mellin transform. -/
def zetaRemainderKernel (t x : ℝ) : ℂ :=
  if 1 < x then zetaSum x t -
    Complex.exp ((Real.log x : ℂ) * ((t : ℂ) * I + 1)) / ((t : ℂ) * I + 1) else 0

theorem zetaRemainderKernel_eq (t : ℝ) {x : ℝ} (hx : 1 < x) :
    zetaRemainderKernel t x =
      zetaSum x t - (x : ℂ) ^ ((t : ℂ) * I + 1) / ((t : ℂ) * I + 1) := by
  rw [zetaRemainderKernel, if_pos hx,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0)),
    ← Complex.ofReal_log (by linarith : 0 ≤ x)]

theorem zetaRemainderKernel_eq_zero (t : ℝ) {x : ℝ} (hx : x ≤ 1) :
    zetaRemainderKernel t x = 0 := by simp [zetaRemainderKernel, not_lt.mpr hx]

theorem norm_zetaRemainderKernel_le (t x : ℝ) :
    ‖zetaRemainderKernel t x‖ ≤ 4 * (1 + t ^ 2) := by
  by_cases hx : 1 < x
  · rw [zetaRemainderKernel_eq t hx]
    exact norm_zetaSum_sub_powerMain_le t hx.le
  · rw [zetaRemainderKernel_eq_zero t (not_lt.mp hx), norm_zero]
    positivity

theorem measurable_zetaRemainderKernel (t : ℝ) : Measurable (zetaRemainderKernel t) := by
  apply Measurable.ite measurableSet_Ioi
  · exact (measurable_zetaSum t).sub (by fun_prop)
  · exact measurable_const

theorem locallyIntegrableOn_zetaRemainderKernel (t : ℝ) :
    LocallyIntegrableOn (zetaRemainderKernel t) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _ hk
  apply IntegrableOn.of_bound hk.measure_lt_top
  · exact (measurable_zetaRemainderKernel t).aestronglyMeasurable.restrict
  · filter_upwards with x
    exact norm_zetaRemainderKernel_le t x

theorem zetaRemainderKernel_isBigO_atTop (t : ℝ) :
    zetaRemainderKernel t =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
  apply IsBigO.of_bound (4 * (1 + t ^ 2))
  filter_upwards with x
  simpa only [Real.rpow_zero, norm_one, mul_one] using norm_zetaRemainderKernel_le t x

theorem zetaRemainderKernel_isBigO_zero (t b : ℝ) :
    zetaRemainderKernel t =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  rw [zetaRemainderKernel_eq_zero t hx.2.le, norm_zero]
  positivity

/-- Convergent, pole-subtracted Mellin transform of the original sum. -/
def zetaRemainderMellin (t : ℝ) (s : ℂ) : ℂ := mellin (zetaRemainderKernel t) (-s)

theorem mellinConvergent_zetaRemainderKernel (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (zetaRemainderKernel t) (-s) :=
  mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrableOn_zetaRemainderKernel t)
    (by simpa using zetaRemainderKernel_isBigO_atTop t) (by simpa using hs)
    (zetaRemainderKernel_isBigO_zero t (-s.re - 1)) (by simp)

theorem differentiableAt_zetaRemainderMellin (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (zetaRemainderMellin t) s := by
  have h := mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrableOn_zetaRemainderKernel t)
    (by simpa using zetaRemainderKernel_isBigO_atTop t) (s := -s) (by simpa using hs)
    (zetaRemainderKernel_isBigO_zero t (-s.re - 1)) (by simp)
  exact h.comp s (hasDerivAt_neg s).differentiableAt

theorem zetaRemainderMellin_eq_integral (t : ℝ) (s : ℂ) :
    zetaRemainderMellin t s = ∫ x in Ioi (1 : ℝ),
      (zetaSum x t - (x : ℂ) ^ ((t : ℂ) * I + 1) / ((t : ℂ) * I + 1)) *
        (x : ℂ) ^ (-(s + 1)) := by
  have hz : ∀ x ∈ Ioc (0 : ℝ) 1,
      (x : ℂ) ^ (-s - 1) * zetaRemainderKernel t x = 0 := by
    intro x hx
    rw [zetaRemainderKernel_eq_zero t hx.2, mul_zero]
  have h := integral_union_eq_left_of_forall (μ := volume) (s := Ioi (1 : ℝ))
    measurableSet_Ioc hz
  rw [union_comm, Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] at h
  unfold zetaRemainderMellin mellin
  simp only [smul_eq_mul]
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [zetaRemainderKernel_eq t hx, mul_comm]
  congr 2
  ring

theorem integrableOn_zetaRemainder_cpow (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      (zetaSum x t - (x : ℂ) ^ ((t : ℂ) * I + 1) / ((t : ℂ) * I + 1)) *
        (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-s - 1) * zetaRemainderKernel t x) (Ioi 0) :=
    by simpa only [MellinConvergent, smul_eq_mul] using mellinConvergent_zetaRemainderKernel t hs
  apply (h.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))).congr_fun
    _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [zetaRemainderKernel_eq t hx, mul_comm]
  congr 2
  ring

/-- The pole-subtracted transform agrees with the convergent Dirichlet series
on its original right half-plane, with the subtraction term explicit. -/
theorem zetaRemainderMellin_eq_of_one_lt_re (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    zetaRemainderMellin t s = riemannZeta (s - (t : ℂ) * I) / s -
      1 / (((t : ℂ) * I + 1) * (s - ((t : ℂ) * I + 1))) := by
  let c : ℂ := (t : ℂ) * I + 1
  have hpow : (c - s - 1).re < -1 := by
    dsimp [c]
    simp only [mul_I_re, ofReal_im, neg_zero, zero_add]
    linarith
  have hid (x : ℝ) (hx : 1 < x) :
      (x : ℂ) ^ c / c * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (c - s - 1) / c := by
    rw [div_mul_eq_mul_div, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0))]
    congr 2
    ring
  have hp : IntegrableOn (fun x : ℝ => (x : ℂ) ^ c / c * (x : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    have hbase : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (c - s - 1) / c) (Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt hpow zero_lt_one).div_const c
    apply hbase.congr_fun _ measurableSet_Ioi
    intro x hx
    exact (hid x hx).symm
  have hIp : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ c / c * (x : ℂ) ^ (-(s + 1))) =
      1 / (c * (s - c)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hid, integral_div,
      integral_Ioi_cpow_of_lt hpow zero_lt_one, Complex.ofReal_one, one_cpow]
    rw [show c - s - 1 + 1 = -(s - c) by ring, neg_div_neg_eq, div_div, mul_comm]
  rw [zetaRemainderMellin_eq_integral]
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_zetaSum_cpow t hs) hp, integral_zetaSum_cpow t hs, hIp]

/-- Analytic continuation of the genuine remainder integral with both removable
factors retained; no product formula or transform identity is assumed. -/
theorem zetaRemainderMellin_pole_removed (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s * (s - ((t : ℂ) * I + 1)) * zetaRemainderMellin t s =
      RiemannZeta.GuthMaynard.regularizedRiemannZeta (s - (t : ℂ) * I) -
        s / ((t : ℂ) * I + 1) := by
  let c : ℂ := (t : ℂ) * I + 1
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hleft : AnalyticOnNhd ℂ (fun z : ℂ => z * (z - c) * zetaRemainderMellin t z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const c)).mul
      (differentiableAt_zetaRemainderMellin t hz)).differentiableWithinAt
  have hright : AnalyticOnNhd ℂ (fun z : ℂ =>
      RiemannZeta.GuthMaynard.regularizedRiemannZeta (z - (t : ℂ) * I) - z / c) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z _
    exact (((RiemannZeta.GuthMaynard.differentiableAt_regularizedRiemannZeta
      (z - (t : ℂ) * I)).comp z (differentiableAt_id.sub_const _)).sub
      (differentiableAt_id.div_const c)).differentiableWithinAt
  have heq : (fun z : ℂ => z * (z - c) * zetaRemainderMellin t z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => RiemannZeta.GuthMaynard.regularizedRiemannZeta
        (z - (t : ℂ) * I) - z / c) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z | 1 < z.re})] with z hz
    have hz0 : z ≠ 0 := Complex.ne_zero_of_one_lt_re hz
    have hc : c ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [c] at this
    have hzc : z - c ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [c] at this
      linarith
    have hz1 : z - (t : ℂ) * I ≠ 1 := by
      intro h
      apply hzc
      dsimp [c]
      linear_combination h
    rw [zetaRemainderMellin_eq_of_one_lt_re t hz,
      RiemannZeta.GuthMaynard.regularizedRiemannZeta, Function.update_of_ne hz1]
    change z * (z - c) * (riemannZeta (z - (t : ℂ) * I) / z - 1 / (c * (z - c))) = _
    have hdiff : z - (t : ℂ) * I - 1 = z - c := by dsimp [c]; ring
    rw [hdiff]
    field_simp
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt 0).isPreconnected (by change (0 : ℝ) < 2; norm_num) heq hs

/-- The actual Mellin remainder throughout the right half-plane, away from the
displayed pole. Its integral is absolutely convergent on this entire domain. -/
theorem zetaRemainderMellin_eq (t : ℝ) {s : ℂ} (hs : 0 < s.re)
    (hp : s ≠ (t : ℂ) * I + 1) :
    zetaRemainderMellin t s = riemannZeta (s - (t : ℂ) * I) / s -
      1 / (((t : ℂ) * I + 1) * (s - ((t : ℂ) * I + 1))) := by
  have h := zetaRemainderMellin_pole_removed t hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hc : (t : ℂ) * I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hsc : s - ((t : ℂ) * I + 1) ≠ 0 := sub_ne_zero.mpr hp
  have hp' : s - (t : ℂ) * I ≠ 1 := by
    intro h
    apply hsc
    linear_combination h
  rw [RiemannZeta.GuthMaynard.regularizedRiemannZeta, Function.update_of_ne hp'] at h
  field_simp at h ⊢
  linear_combination h

/-- Full real-line remainder: the exponential main term is subtracted also at
negative logarithmic cutoffs, where the original finite sum vanishes. -/
def zetaExpRemainder (t u : ℝ) : ℂ := zetaSum (Real.exp u) t -
  Complex.exp (((t : ℂ) * I + 1) * u) / ((t : ℂ) * I + 1)

theorem zetaExpRemainder_eq_power (t u : ℝ) :
    zetaExpRemainder t u = zetaSum (Real.exp u) t -
      (Real.exp u : ℂ) ^ ((t : ℂ) * I + 1) / ((t : ℂ) * I + 1) := by
  rw [zetaExpRemainder, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, mul_comm]

theorem zetaExpRemainder_of_neg (t : ℝ) {u : ℝ} (hu : u < 0) :
    zetaExpRemainder t u = -Complex.exp (((t : ℂ) * I + 1) * u) / ((t : ℂ) * I + 1) := by
  rw [zetaExpRemainder, zetaSum_eq_zero_of_lt_one
    (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu), zero_sub, neg_div]

theorem norm_zetaExpRemainder_le (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖zetaExpRemainder t u‖ ≤ 4 * (1 + t ^ 2) := by
  rw [zetaExpRemainder_eq_power]
  exact norm_zetaSum_sub_powerMain_le t (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu)

theorem measurable_zetaExpRemainder (t : ℝ) : Measurable (zetaExpRemainder t) :=
  ((measurable_zetaSum t).comp Real.measurable_exp).sub (by fun_prop)

private theorem regularized_exp_image : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu
  · intro hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log (zero_lt_one.trans hx)⟩

private theorem regularized_exp_jacobian (t u : ℝ) (s : ℂ) :
    (Real.exp u : ℂ) *
      ((zetaSum (Real.exp u) t - (Real.exp u : ℂ) ^ ((t : ℂ) * I + 1) /
        ((t : ℂ) * I + 1)) * (Real.exp u : ℂ) ^ (-(s + 1))) =
      zetaExpRemainder t u * Complex.exp (-s * u) := by
  rw [← zetaExpRemainder_eq_power, mul_left_comm]
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring

theorem integral_zetaExpRemainder_positive (t : ℝ) (s : ℂ) :
    (∫ u in Ioi (0 : ℝ), zetaExpRemainder t u * Complex.exp (-s * u)) =
      zetaRemainderMellin t s := by
  rw [zetaRemainderMellin_eq_integral, ← regularized_exp_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, regularized_exp_jacobian]

theorem integrableOn_zetaExpRemainder_positive (t : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => zetaExpRemainder t u * Complex.exp (-s * u)) (Ioi 0) := by
  have h := integrableOn_zetaRemainder_cpow t hs
  rw [← regularized_exp_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      Real.exp_injective.injOn] at h
  apply h.congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, regularized_exp_jacobian]

private theorem regularized_negative_integrand (t : ℝ) (s : ℂ) {u : ℝ} (hu : u < 0) :
    zetaExpRemainder t u * Complex.exp (-s * u) =
      -Complex.exp ((((t : ℂ) * I + 1) - s) * u) / ((t : ℂ) * I + 1) := by
  rw [zetaExpRemainder_of_neg t hu, div_mul_eq_mul_div, neg_mul, ← Complex.exp_add]
  congr 3
  ring

theorem integrableOn_zetaExpRemainder_negative (t : ℝ) {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun u : ℝ => zetaExpRemainder t u * Complex.exp (-s * u)) (Iio 0) := by
  have hc : 0 < (((t : ℂ) * I + 1) - s).re := by simpa using sub_pos.mpr hs
  have h : IntegrableOn (fun u : ℝ =>
      -Complex.exp ((((t : ℂ) * I + 1) - s) * u) / ((t : ℂ) * I + 1)) (Iio 0) :=
    (((integrableOn_exp_mul_complex_Iic hc 0).mono_set Iio_subset_Iic_self).neg).div_const _
  exact h.congr_fun (fun u hu => (regularized_negative_integrand t s hu).symm) measurableSet_Iio

theorem integral_zetaExpRemainder_negative (t : ℝ) {s : ℂ} (hs : s.re < 1) :
    (∫ u in Iio (0 : ℝ), zetaExpRemainder t u * Complex.exp (-s * u)) =
      1 / (((t : ℂ) * I + 1) * (s - ((t : ℂ) * I + 1))) := by
  have hc : 0 < (((t : ℂ) * I + 1) - s).re := by simpa using sub_pos.mpr hs
  rw [setIntegral_congr_fun measurableSet_Iio (fun u hu => regularized_negative_integrand t s hu),
    integral_div, integral_neg, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic hc 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (t : ℂ) * I + 1 - s = -(s - ((t : ℂ) * I + 1)) by ring,
    div_neg, neg_neg, div_div, mul_comm]

/-- Absolute convergence of the regularized transform throughout the open strip. -/
theorem integrable_zetaExpRemainder (t : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (fun u : ℝ => zetaExpRemainder t u * Complex.exp (-s * u)) := by
  have hpos := (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (integrableOn_zetaExpRemainder_positive t hs0)
  simpa only [Iio_union_Ici, integrableOn_univ] using
    (integrableOn_zetaExpRemainder_negative t hs1).union hpos

/-- The regularized full-line transform is exactly the shifted zeta quotient
inside the strip. The two explicit pole fractions cancel, rather than vanish. -/
theorem integral_zetaExpRemainder (t : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (∫ u : ℝ, zetaExpRemainder t u * Complex.exp (-s * u)) =
      riemannZeta (s - (t : ℂ) * I) / s := by
  have hp : s ≠ (t : ℂ) * I + 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, mul_I_re, ofReal_im, neg_zero, zero_add, one_re] at this
    linarith
  rw [← integral_add_compl (measurableSet_Iic (a := (0 : ℝ)))
      (integrable_zetaExpRemainder t hs0 hs1), compl_Iic,
    integral_Iic_eq_integral_Iio, integral_zetaExpRemainder_negative t hs1,
    integral_zetaExpRemainder_positive, zetaRemainderMellin_eq t hs0 hp]
  ring

end
end DongWangWangZhang2026
