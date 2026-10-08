import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Genuine L2 differentiation from bounded original pointwise difference quotients -/

namespace Dubon2026

noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- The genuine complex L2 inner product of two original representatives is their actual integral pairing. -/
theorem complex_toLp_inner {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℂ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    inner ℂ (hF.toLp F) (hG.toLp G) = ∫ x, inner ℂ (F x) (G x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Actual pointwise convergence with a uniform finite-measure difference bound implies convergence of the original L2 representatives. -/
theorem toLp_tendsto_of_uniform_difference_bound {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → X → ℂ) (G : X → ℂ) (hF : ∀ i, MemLp (F i) 2 μ) (hG : MemLp G 2 μ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i x, ‖F i x - G x‖ ≤ B)
    (hlim : ∀ x, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hG.toLp G)) := by
  have hi : Tendsto (fun i => ∫ x, inner ℂ (F i x - G x) (F i x - G x) ∂μ) l (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ)
      (F := fun i x => inner ℂ (F i x - G x) (F i x - G x))
      (f := fun _ : X => (0 : ℂ))
      (fun _ : X => B ^ 2)
      (Eventually.of_forall (fun i =>
        ((hF i).aestronglyMeasurable.sub hG.aestronglyMeasurable).inner
          ((hF i).aestronglyMeasurable.sub hG.aestronglyMeasurable)))
      (Eventually.of_forall (fun i => ae_of_all μ (fun x =>
        (norm_inner_le_norm (𝕜 := ℂ) (F i x - G x) (F i x - G x)).trans
          (by simpa only [pow_two] using mul_le_mul (hB i x) (hB i x) (norm_nonneg _) hB0))))
      (integrable_const (B ^ 2))
      (ae_of_all μ (fun x => by
        simpa only [sub_self, inner_zero_left] using
          ((hlim x).sub (tendsto_const_nhds (x := G x))).inner (𝕜 := ℂ) ((hlim x).sub (tendsto_const_nhds (x := G x)))))
    simpa only [integral_zero] using ht
  have he (i : ι) :
      inner ℂ ((hF i).toLp (F i) - hG.toLp G) ((hF i).toLp (F i) - hG.toLp G) =
        ∫ x, inner ℂ (F i x - G x) (F i x - G x) ∂μ := by
    rw [← MemLp.toLp_sub, complex_toLp_inner]
    rfl
  have hn : Tendsto (fun i => ‖(hF i).toLp (F i) - hG.toLp G‖ ^ 2) l (𝓝 0) := by
    have hr := Complex.continuous_re.continuousAt.tendsto.comp hi
    change Tendsto (fun i => (∫ x, inner ℂ (F i x - G x) (F i x - G x) ∂μ).re) l
      (𝓝 (0 : ℝ)) at hr
    have heq (i : ι) : (∫ x, inner ℂ (F i x - G x) (F i x - G x) ∂μ).re =
        ‖(hF i).toLp (F i) - hG.toLp G‖ ^ 2 := by
      rw [← he i]
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    simpa only [heq] using hr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hn

/-- A proved bounded family of original difference quotients promotes the actual pointwise derivative to the genuine L2 derivative. -/
theorem hasDerivAt_toLp_of_bounded_difference_quotients {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F : ℝ → X → ℂ) (D : X → ℂ)
    (hF : ∀ t, MemLp (F t) 2 μ) (hD : MemLp D 2 μ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => F t x) (D x) 0)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t x, ‖(t⁻¹ : ℝ) • (F t x - F 0 x) - D x‖ ≤ B) :
    HasDerivAt (fun t : ℝ => (hF t).toLp (F t)) (hD.toLp D) 0 := by
  let S : ℝ → X → ℂ := fun t x => (t⁻¹ : ℝ) • (F t x - F 0 x)
  have hS (t : ℝ) : MemLp (S t) 2 μ := ((hF t).sub (hF 0)).const_smul (t⁻¹ : ℝ)
  have ht := toLp_tendsto_of_uniform_difference_bound (l := 𝓝[≠] (0 : ℝ)) S D hS hD hB0 hB
    (fun x => by simpa only [zero_add] using (hd x).tendsto_slope_zero)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [S, hS, MemLp.toLp_const_smul, MemLp.toLp_sub, zero_add] using ht

/-- Actual pointwise derivatives are almost everywhere strongly measurable as limits of the original measurable difference quotients. -/
theorem aestronglyMeasurable_pointwise_derivative {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (F : ℝ → X → ℂ) (D : X → ℂ)
    (hF : ∀ t, AEStronglyMeasurable (F t) μ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => F t x) (D x) 0) : AEStronglyMeasurable D μ := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ))
    (f := fun t x => (t⁻¹ : ℝ) • (F t x - F 0 x))
    (fun t => ((hF t).sub (hF 0)).const_smul (t⁻¹ : ℝ))
  exact ae_of_all μ (fun x => by simpa only [zero_add] using (hd x).tendsto_slope_zero)

/-- Actual bounded pointwise derivatives are genuine L2 vectors on every finite measure space. -/
theorem memLp_pointwise_derivative {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F : ℝ → X → ℂ) (D : X → ℂ)
    (hF : ∀ t, AEStronglyMeasurable (F t) μ)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => F t x) (D x) 0)
    (C : ℝ) (hC : ∀ x, ‖D x‖ ≤ C) : MemLp D 2 μ :=
  MemLp.of_bound (aestronglyMeasurable_pointwise_derivative F D hF hd) C (ae_of_all μ hC)

/-- A genuine pointwise Lipschitz increment bound and derivative bound give a uniform bound for all original difference-quotient errors. -/
theorem difference_quotient_error_bound (F : ℝ → ℂ) (D : ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖F t - F 0‖ ≤ C * |t|) (hD : ‖D‖ ≤ C) (t : ℝ) :
    ‖(t⁻¹ : ℝ) • (F t - F 0) - D‖ ≤ 2 * C := by
  have hs : ‖(t⁻¹ : ℝ) • (F t - F 0)‖ ≤ C := by
    by_cases ht : t = 0
    · simpa [ht] using hC0
    · calc
        _ = |t|⁻¹ * ‖F t - F 0‖ := by rw [norm_smul, norm_inv, Real.norm_eq_abs]
        _ ≤ |t|⁻¹ * (C * |t|) :=
          mul_le_mul_of_nonneg_left (hC t) (inv_nonneg.mpr (abs_nonneg t))
        _ = C := by field_simp
  exact (norm_sub_le _ _).trans (by linarith)

end
end Dubon2026
