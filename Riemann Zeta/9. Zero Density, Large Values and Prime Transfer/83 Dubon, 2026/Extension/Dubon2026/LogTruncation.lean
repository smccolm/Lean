import Dubon2026.TorusJensen
import Dubon2026.DirichletZeros
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Truncated logarithmic means and the Haar truncation limit -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem analyticAt_vertical_dirichletSum (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => dirichletSum a N ((σ : ℂ) + Complex.I * u)) t := by
  apply (analyticAt_dirichletSum a N _).restrictScalars.comp
  exact analyticAt_const.add (analyticAt_const.mul (Complex.ofRealCLM.analyticAt t))

theorem intervalIntegrable_vertical_log (a : ℕ → ℂ) (N : ℕ) (σ left right : ℝ) :
    IntervalIntegrable (fun t => Real.log ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖)
      volume left right := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  exact (analyticAt_vertical_dirichletSum a N σ t).meromorphicAt

theorem countable_dirichletZeros {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    {s : ℂ | dirichletSum a N s = 0}.Countable := by
  have hd : IsDiscrete {s : ℂ | dirichletSum a N s = 0} := by
    simpa only [Set.inter_univ] using
      (isDiscrete_of_codiscreteWithin (dirichletSum_eventually_ne_zero_codiscrete hN ha))
  haveI : DiscreteTopology {s : ℂ | dirichletSum a N s = 0} :=
    isDiscrete_iff_discreteTopology.mp hd
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

theorem vertical_dirichletSum_ne_zero_ae {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∀ᵐ t : ℝ, dirichletSum a N ((σ : ℂ) + Complex.I * t) ≠ 0 := by
  have hinj : Function.Injective (fun t : ℝ => (σ : ℂ) + Complex.I * t) := by
    intro x y h
    simpa using congrArg Complex.im h
  have hc := (countable_dirichletZeros hN ha).preimage hinj
  rw [ae_iff]
  simpa only [not_not] using hc.measure_zero volume

/-- The source's symmetric finite-height logarithmic mean, with actual Dirichlet coefficients. -/
def verticalLogMean (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) : ℝ :=
  (2 * T)⁻¹ * ∫ t in -T..T, Real.log ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖

theorem tendsto_real_torusAverage (N : ℕ) (f : C(PrimeTorus N, ℝ)) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T, f (primeTorusFlow N t))
      atTop (𝓝 (∫ z, f z ∂torusHaar N)) := by
  let g : C(PrimeTorus N, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_torusAverage N g)
  change Tendsto (fun T => (torusAverage N g T).re) atTop (𝓝 (∫ z, g z ∂torusHaar N).re) at h
  simpa only [torusAverage, symmetricAverage, g, ContinuousMap.coe_mk,
    intervalIntegral.integral_ofReal, integral_complex_ofReal, Complex.real_smul,
    Complex.ofReal_re, Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero] using h

/-- Continuous truncation of the real logarithm at a positive modulus threshold. -/
def truncatedLogNorm (ε : ℝ) (hε : 0 < ε) : C(ℂ, ℝ) where
  toFun z := Real.log (max ‖z‖ ε)
  continuous_toFun := (continuous_norm.max continuous_const).log
    (fun _ => ne_of_gt (lt_of_lt_of_le hε (le_max_right _ _)))

theorem tendsto_truncated_vertical_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log (max ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖ ε)) atTop
      (𝓝 (∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N)) := by
  have h := tendsto_real_torusAverage N ((truncatedLogNorm ε hε).comp (bohrOnTorus a N σ))
  simpa only [ContinuousMap.comp_apply, truncatedLogNorm, ContinuousMap.coe_mk,
    bohrOnTorus_verticalFlow] using h

theorem abs_log_max_le_abs_log {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (max x ε)| ≤ |Real.log x| := by
  rcases le_total ε x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, abs_of_nonpos (Real.log_nonpos hε.le hε1),
      abs_of_nonpos (Real.log_nonpos hx.le (h.trans hε1))]
    exact neg_le_neg (Real.log_le_log hx h)

theorem tendsto_haar_truncated_log {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (σ : ℝ) :
    Tendsto (fun ε : ℝ => ∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N)
      (𝓝[>] 0) (𝓝 (haarLogPotential a N σ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => |Real.log ‖bohrOnTorus a N σ z‖|)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((truncatedLogNorm ε hε).continuous.comp (bohrOnTorus a N σ).continuous).aestronglyMeasurable
  · have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ≤ 1 :=
      ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds).mono
        (fun _ h => h.le)
    filter_upwards [self_mem_nhdsWithin, he] with ε hε hε1
    filter_upwards [bohrOnTorus_ne_zero_ae hN ha σ] with z hz
    exact abs_log_max_le_abs_log (norm_pos_iff.mpr hz) hε hε1
  · exact (integrable_bohrOnTorus_log a N σ).abs
  · filter_upwards [bohrOnTorus_ne_zero_ae hN ha σ] with z hz
    have hx : 0 < ‖bohrOnTorus a N σ z‖ := norm_pos_iff.mpr hz
    have hc : ContinuousAt (fun ε : ℝ => Real.log (max ‖bohrOnTorus a N σ z‖ ε)) 0 :=
      (continuous_const.max continuous_id).continuousAt.log (by simpa only [id_eq, max_eq_left hx.le] using hx.ne')
    simpa only [max_eq_left hx.le] using hc.tendsto.mono_left nhdsWithin_le_nhds


theorem continuous_vertical_dirichletSum (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => dirichletSum a N ((σ : ℂ) + Complex.I * t)) :=
  continuous_iff_continuousAt.mpr (fun t => (analyticAt_vertical_dirichletSum a N σ t).continuousAt)

theorem verticalLogMean_le_truncated {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (ha : a 1 ≠ 0) (σ : ℝ) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    verticalLogMean a N σ T ≤ (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log (max ‖dirichletSum a N ((σ : ℂ) + Complex.I * t)‖ ε) := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (mul_nonneg (by norm_num) hT))
  apply intervalIntegral.integral_mono_ae (by linarith)
    (intervalIntegrable_vertical_log a N σ (-T) T)
    (((truncatedLogNorm ε hε).continuous.comp
      (continuous_vertical_dirichletSum a N σ)).intervalIntegrable _ _)
  filter_upwards [vertical_dirichletSum_ne_zero_ae hN ha σ] with t ht
  exact Real.log_le_log (norm_pos_iff.mpr ht) (le_max_left _ _)

theorem eventually_verticalLogMean_le_haar_add {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, verticalLogMean a N σ T ≤ haarLogPotential a N σ + δ := by
  have he := (tendsto_order.mp (tendsto_haar_truncated_log hN ha σ)).2
    (haarLogPotential a N σ + δ / 2) (by linarith)
  have hex : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧
      (∫ z, Real.log (max ‖bohrOnTorus a N σ z‖ ε) ∂torusHaar N) <
        haarLogPotential a N σ + δ / 2 := by
    filter_upwards [self_mem_nhdsWithin, he] with ε hε hh using ⟨hε, hh⟩
  obtain ⟨ε, hε, hi⟩ := hex.exists
  have ht := (tendsto_order.mp (tendsto_truncated_vertical_log a N σ hε)).2
    (haarLogPotential a N σ + δ) (by linarith)
  filter_upwards [eventually_ge_atTop (0 : ℝ), ht] with T hT hmean
  exact (verticalLogMean_le_truncated hN ha σ hT hε).trans hmean.le

end

end Dubon2026
