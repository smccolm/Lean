import Dubon2026.LeadingBohrTerm

/-! # Logarithmic integral convergence near a nonvanishing constant-modulus limit -/

namespace Dubon2026

open MeasureTheory Filter
open scoped Topology

theorem tendsto_integral_log_of_constant_modulus_limit
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {ι : Type*} {l : Filter ι} {F : ι → C(X, ℂ)} {g : C(X, ℂ)} {c : ℝ}
    (hc : 0 < c) (hg : ∀ x, ‖g x‖ = c) (hF : Tendsto F l (𝓝 g))
    (hi : ∀ i, Integrable (fun x => Real.log ‖F i x‖) μ) :
    Tendsto (fun i => ∫ x, Real.log ‖F i x‖ ∂μ) l (𝓝 (Real.log c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_log hc.ne') (ε / 2) (half_pos hε)
  filter_upwards [(Metric.tendsto_nhds.mp hF) δ hδ] with i hdist
  have hpoint (x : X) : ‖Real.log ‖F i x‖ - Real.log c‖ ≤ ε / 2 := by
    apply le_of_lt
    apply hb
    rw [Real.dist_eq, ← hg x]
    exact (abs_norm_sub_norm_le (F i x) (g x)).trans_lt
      (((F i - g).norm_coe_le_norm x).trans_lt (by simpa only [dist_eq_norm] using hdist))
  have hbint := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
  rw [integral_sub (hi i) (integrable_const (Real.log c)), integral_const] at hbint
  simp only [probReal_univ, one_smul, mul_one] at hbint
  exact hbint.trans_lt (half_lt_self hε)

end Dubon2026
