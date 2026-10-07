import Dubon2026.NewmanRectangle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Dominated convergence on the genuine left analytic Tauberian contour -/

namespace Dubon2026

open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- Actual exponential damping sends any integrable amplitude to zero when its phase lies strictly left almost everywhere. -/
theorem newman_damped_integral_tendsto_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A b : α → ℂ} (hA : Integrable A μ)
    (hb : AEStronglyMeasurable b μ) (hneg : ∀ᵐ x ∂μ, (b x).re < 0) :
    Tendsto (fun T : ℝ => ∫ x, A x * Complex.exp ((T : ℂ) * b x) ∂μ) atTop (𝓝 0) := by
  have hm : ∀ᶠ T : ℝ in atTop, AEStronglyMeasurable
      (fun x => A x * Complex.exp ((T : ℂ) * b x)) μ :=
    .of_forall (fun T => hA.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp_aestronglyMeasurable (hb.const_mul (T : ℂ))))
  have hh : ∀ᶠ T : ℝ in atTop, ∀ᵐ x ∂μ,
      ‖A x * Complex.exp ((T : ℂ) * b x)‖ ≤ ‖A x‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    filter_upwards [hneg] with x hx
    simp only [norm_mul, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hT hx.le))
  have hl : ∀ᵐ x ∂μ, Tendsto (fun T : ℝ => A x * Complex.exp ((T : ℂ) * b x)) atTop (𝓝 0) := by
    filter_upwards [hneg] with x hx
    have he : Tendsto (fun T : ℝ => Complex.exp ((T : ℂ) * b x)) atTop (𝓝 0) := by
      apply Complex.tendsto_exp_nhds_zero_iff.mpr
      simpa using tendsto_id.atTop_mul_const_of_neg hx
    simpa using tendsto_const_nhds.mul he
  simpa using tendsto_integral_filter_of_dominated_convergence (fun x => ‖A x‖) hm hh hA.norm hl

/-- The actual kernel is continuous away from its only possible pole. -/
theorem continuousOn_newmanKernel (R : ℝ) : ContinuousOn (newmanKernel R) ({0}ᶜ : Set ℂ) := by
  unfold newmanKernel
  apply ContinuousOn.div (by fun_prop) continuousOn_id
  intro z hz
  exact hz

/-- The actual contour integrand is continuous on every pole-free part of the continuation domain. -/
theorem continuousOn_newmanContourIntegrand {G : ℂ → ℂ} {U : Set ℂ}
    (hG : ContinuousOn G U) (hU : ∀ z ∈ U, z ≠ 0) (T R : ℝ) :
    ContinuousOn (newmanContourIntegrand G T R) U :=
  (hG.mul (by fun_prop)).mul ((continuousOn_newmanKernel R).mono hU)

/-- On a horizontal edge strictly left of the axis, the actual analytic contour integral tends to zero. -/
theorem newman_horizontal_left_tendsto_zero {G : ℂ → ℂ} {d R y : ℝ}
    (hd : 0 < d) (hy : y ≠ 0) (hG : ContinuousOn G {z : ℂ | -d ≤ z.re}) :
    Tendsto (fun T : ℝ => HIntegral (newmanContourIntegrand G T R) (-d) 0 y) atTop (𝓝 0) := by
  let b : ℝ → ℂ := fun x => (x : ℂ) + y * I
  let A : ℝ → ℂ := fun x => G (b x) * newmanKernel R (b x)
  have hb : Continuous b := by fun_prop
  have hg : ContinuousOn (fun x => G (b x)) (Icc (-d) 0) := hG.comp hb.continuousOn (by
    intro x hx
    simpa [b] using hx.1)
  have hk : ContinuousOn (fun x => newmanKernel R (b x)) (Icc (-d) 0) :=
    (continuousOn_newmanKernel R).comp hb.continuousOn (by
      intro x _ hz
      have he := congrArg Complex.im hz
      exact hy (by simpa [b] using he))
  have hi : IntegrableOn A (Ioc (-d) 0) := (hg.mul hk).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-d) 0)), (b x).re < 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, (volume.restrict (Ioc (-d) 0)).ae_ne (0 : ℝ)] with x hx hx0
    simpa [b] using lt_of_le_of_ne hx.2 hx0
  have hh := newman_damped_integral_tendsto_zero hi hb.aestronglyMeasurable hn
  have he (T : ℝ) : HIntegral (newmanContourIntegrand G T R) (-d) 0 y =
      ∫ x : ℝ in Ioc (-d) 0, A x * Complex.exp ((T : ℂ) * b x) := by
    rw [HIntegral, intervalIntegral.integral_of_le (by linarith)]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [newmanContourIntegrand, A, b]
    ring
  simpa only [he] using hh

/-- On a fixed negative vertical edge, the actual analytic contour integral tends to zero. -/
theorem newman_vertical_left_tendsto_zero {G : ℂ → ℂ} {d R : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hG : ContinuousOn G {z : ℂ | -d ≤ z.re}) :
    Tendsto (fun T : ℝ => VIntegral (newmanContourIntegrand G T R) (-d) (-R) R) atTop (𝓝 0) := by
  let b : ℝ → ℂ := fun y => (-d : ℂ) + y * I
  let A : ℝ → ℂ := fun y => G (b y) * newmanKernel R (b y)
  have hb : Continuous b := by fun_prop
  have hg : ContinuousOn (fun y => G (b y)) (Icc (-R) R) := hG.comp hb.continuousOn (by
    intro y _
    simp [b])
  have hk : ContinuousOn (fun y => newmanKernel R (b y)) (Icc (-R) R) :=
    (continuousOn_newmanKernel R).comp hb.continuousOn (by
      intro y _ hz
      have he := congrArg Complex.re hz
      have : -d = 0 := by simpa [b] using he
      linarith)
  have hi : IntegrableOn A (Ioc (-R) R) := (hg.mul hk).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-R) R)), (b y).re < 0 := .of_forall (fun y => by simp [b]; linarith)
  have hh := newman_damped_integral_tendsto_zero hi hb.aestronglyMeasurable hn
  have he (T : ℝ) : VIntegral (newmanContourIntegrand G T R) (-d) (-R) R =
      I * ∫ y : ℝ in Ioc (-R) R, A y * Complex.exp ((T : ℂ) * b y) := by
    rw [VIntegral, smul_eq_mul, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [newmanContourIntegrand, A, b]
    simp only [ofReal_neg]
    ring
  simpa only [he, mul_zero] using tendsto_const_nhds.mul hh

/-- All three fixed left edges of the genuine analytic continuation vanish together. -/
theorem newman_left_contour_tendsto_zero {G : ℂ → ℂ} {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hG : ContinuousOn G {z : ℂ | -d ≤ z.re}) :
    Tendsto (fun T : ℝ => newmanLeftContour (newmanContourIntegrand G T R) d R) atTop (𝓝 0) := by
  simpa only [newmanLeftContour, sub_zero] using
    ((newman_horizontal_left_tendsto_zero (R := R) hd (neg_ne_zero.mpr hR.ne') hG).sub
      (newman_horizontal_left_tendsto_zero (R := R) hd hR.ne' hG)).sub
        (newman_vertical_left_tendsto_zero hd hR.le hG)

end
end Dubon2026
