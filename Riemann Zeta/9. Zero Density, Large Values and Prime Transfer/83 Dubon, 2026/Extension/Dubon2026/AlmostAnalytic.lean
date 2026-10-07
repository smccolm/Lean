import Dubon2026.PhaseSturmCount

/-! # Almost-everywhere analyticity survives total division and algebraic branching -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Analyticity almost everywhere is enough for almost-everywhere local constancy of signs. -/
theorem ae_analytic_sign_locally_constant (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {s : Set V} (hf : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ f y) :
    ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y, SignType.sign (f z) = SignType.sign (f y) := by
  have hs := analytic_ae_continuousAt_sign μ
    (s := {y | AnalyticAt ℝ f y}) (fun _ hy => hy)
  have hi := (ae_restrict_iff' (isOpen_analyticAt ℝ f).measurableSet).mp hs
  filter_upwards [hf, ae_restrict_of_ae hi] with y hy hiy
  exact (hiy hy).eventually ((isOpen_discrete {SignType.sign (f y)}).mem_nhds rfl)

/-- Total real inversion is locally analytic off a null set, including regions where f=0. -/
theorem ae_analyticAt_inv (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f : V → ℝ} {s : Set V} (hf : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ f y) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => (f z)⁻¹) y := by
  filter_upwards [hf, ae_analytic_sign_locally_constant μ hf] with y hy hs
  by_cases hz : f y = 0
  · apply (show AnalyticAt ℝ (fun _ : V => (0 : ℝ)) y from analyticAt_const).congr
    filter_upwards [hs] with z hsz
    have hzero : f z = 0 := sign_eq_zero_iff.mp (by simpa only [hz, sign_zero] using hsz)
    simp only [hzero, inv_zero]
  · exact hy.inv hz

theorem ae_analyticAt_div (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f g : V → ℝ} {s : Set V}
    (hf : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ f y)
    (hg : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ g y) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => f z / g z) y := by
  filter_upwards [hf, ae_analyticAt_inv μ hg] with y hy hiy
  simpa only [div_eq_mul_inv] using hy.mul hiy

/-- A zero test of an almost-everywhere analytic function is locally constant almost everywhere. -/
theorem ae_analyticAt_ite_eq_zero (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {f g h : V → ℝ} {s : Set V}
    (hf : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ f y)
    (hg : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ g y)
    (hh : ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ h y) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => if f z = 0 then g z else h z) y := by
  filter_upwards [hg, hh, ae_analytic_sign_locally_constant μ hf] with y hgy hhy hs
  by_cases hz : f y = 0
  · apply hgy.congr
    filter_upwards [hs] with z hsz
    have hzero : f z = 0 := sign_eq_zero_iff.mp (by simpa only [hz, sign_zero] using hsz)
    simp only [hzero, if_true]
  · apply hhy.congr
    filter_upwards [hs] with z hsz
    have hn : f z ≠ 0 := by
      intro he
      apply hz
      exact sign_eq_zero_iff.mp (by simpa only [he, sign_zero] using hsz.symm)
    simp only [hn, if_false]

omit [BorelSpace V] [FiniteDimensional ℝ V] in
/-- A countable collection of analytic formulas can be selected by a locally constant index. -/
theorem ae_analyticAt_nat_index (μ : Measure V) {s : Set V} {f : ℕ → V → ℝ}
    {n : V → ℕ} (hf : ∀ k, ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (f k) y)
    (hn : ∀ᵐ y ∂μ.restrict s, ∀ᶠ z in 𝓝 y, n z = n y) :
    ∀ᵐ y ∂μ.restrict s, AnalyticAt ℝ (fun z => f (n z) z) y := by
  have hall : ∀ᵐ y ∂μ.restrict s, ∀ k, AnalyticAt ℝ (f k) y := ae_all_iff.mpr hf
  filter_upwards [hall, hn] with y hy hny
  apply (hy (n y)).congr
  filter_upwards [hny] with z hz
  rw [hz]

end Dubon2026
