import Dubon2026.SourceOriginalFiniteChartParameters

/-! DUB-17/18 -> original torsion cardinality -> compatible actual
place charts. Record the pointwise order/regularity property already
proved for finite-place parameters, and derive local regularity and
comparisons after subtracting constants, needed for chart transitions. This
property is an internal input to transition lemmas; the actual finite
place producer below proves it without an assumed chart or order model.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Filter SourceCurve
open scoped Topology

theorem originalPlaceEval_zero (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) : originalPlaceEval N ℂ v 0 = 0 := by
  simpa only [map_zero] using originalPlaceEval_algebraMap N ℂ v 0

namespace OriginalChart

/-- Exact order and regularity of the original evaluation along a specified place family. -/
def Orders (N : ℕ) [NeZero N] (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
    MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
    meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = (γ z).ord f ∧
    (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z)

variable {N : ℕ} [NeZero N] {γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)}
variable {U : Set ℂ} {z : ℂ}

theorem Orders.analyticAt (h : Orders N γ U) (hz : z ∈ U) {f : modularFunctionFieldOver N ℂ}
    (hf : f ∈ (γ z).toValuationSubring) : AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z := by
  by_cases hf0 : f = 0
  · subst f
    simp only [originalPlaceEval_zero]
    exact analyticAt_const
  exact (h z hz f hf0).2.2 hf

theorem Orders.eventually_mem (h : Orders N γ U) (hU : U ∈ 𝓝 z)
    {f : modularFunctionFieldOver N ℂ} (hf : f ∈ (γ z).toValuationSubring) :
    ∀ᶠ u in 𝓝 z, f ∈ (γ u).toValuationSubring := by
  by_cases hf0 : f = 0
  · subst f
    exact Eventually.of_forall fun u => zero_mem (γ u).toValuationSubring
  filter_upwards [(h.analyticAt (mem_of_mem_nhds hU) hf).eventually_analyticAt, hU] with u hu huU
  have hn := hu.meromorphicOrderAt_nonneg
  rw [(h u huU f hf0).2.1] at hn
  exact (γ u).mem_of_ord_nonneg (by exact_mod_cast hn)

theorem Orders.meromorphicOrderAt_sub_const (h : Orders N γ U) (hU : U ∈ 𝓝 z)
    {f : modularFunctionFieldOver N ℂ} (hf : f ∈ (γ z).toValuationSubring) (c : ℂ)
    (hfc : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c ≠ 0) :
    meromorphicOrderAt (fun u => originalPlaceEval N ℂ (γ u) f - c) z =
      ((γ z).ord (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) : WithTop ℤ) := by
  rw [← (h z (mem_of_mem_nhds hU) _ hfc).2.1]
  apply meromorphicOrderAt_congr
  exact ((h.eventually_mem hU hf).mono fun u hu =>
    (originalPlaceEval_sub_algebraMap N ℂ (γ u) hu c).symm).filter_mono nhdsWithin_le_nhds

theorem Orders.uniformizer_sub_order (h : Orders N γ U) (hU : U ∈ 𝓝 z)
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (heval : ∀ u ∈ U, originalPlaceEval N ℂ (γ u) v.uniformizer = u) :
    (γ z).ord (v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z) = 1 := by
  have he : (fun u => originalPlaceEval N ℂ (γ u) v.uniformizer) =ᶠ[𝓝 z] id := by
    filter_upwards [hU] with u hu
    exact heval u hu
  have ha : AnalyticAt ℂ (fun u => originalPlaceEval N ℂ (γ u) v.uniformizer) z :=
    analyticAt_id.congr he.symm
  have hmem : v.uniformizer ∈ (γ z).toValuationSubring := by
    have hn := ha.meromorphicOrderAt_nonneg
    rw [(h z (mem_of_mem_nhds hU) _ v.uniformizer_ne_zero).2.1] at hn
    exact (γ z).mem_of_ord_nonneg (by exact_mod_cast hn)
  have hfc : v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z ≠ 0 := by
    intro h0
    apply v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)
    rw [sub_eq_zero.mp h0]
    exact isAlgebraic_algebraMap z
  have ho := h.meromorphicOrderAt_sub_const hU hmem z hfc
  have he' : (fun u => originalPlaceEval N ℂ (γ u) v.uniformizer - z) =ᶠ[𝓝[≠] z]
      (fun u : ℂ => u - z) := (he.mono fun u hu => congrArg (fun a => a - z) hu).filter_mono nhdsWithin_le_nhds
  rw [meromorphicOrderAt_congr he', meromorphicOrderAt_id_sub_const] at ho
  exact WithTop.coe_injective ho.symm

end OriginalChart

theorem original_finite_place_parameter_package (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = v ∧ OriginalChart.Orders N γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, (γ z).ord
        (v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z) = 1) := by
  obtain ⟨ρ, γ, hρ, h0, _, heval, ho⟩ := original_finite_place_chart_parameter N v hv
  refine ⟨ρ, γ, hρ, h0, ho, ?_⟩
  intro z hz
  exact OriginalChart.Orders.uniformizer_sub_order ho (Metric.isOpen_ball.mem_nhds hz) v heval

end
end Dubon2026.SourceFunctionField
