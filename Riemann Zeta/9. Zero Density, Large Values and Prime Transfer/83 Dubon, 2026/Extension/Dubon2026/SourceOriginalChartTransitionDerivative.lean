import Dubon2026.SourceOriginalChartDifferentials
import Dubon2026.SourceMeromorphicRemovableCharts

/-! DUB-17/18 -> geometric cell dissection -> original normal coordinates.
Transport the normal coordinate from its central chart to every chart on
its source. The existing manifold transition theorem supplies analyticity;
the inverse transition proves its derivative is nonzero.
Adapted from ChartTransition in S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter
open scoped Manifold ContDiff Topology
attribute [local instance] placeTopology placeChartedSpace place_isManifold
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem analyticAt_original_chart_transition (v w : Place ℂ F) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) w).target)
    (hv : (extChartAt 𝓘(ℂ, ℂ) w).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z :=
  MeromorphicCompact.analyticAt_transition v w hz hv

theorem deriv_original_chart_transition_ne_zero (v w : Place ℂ F)
    (hw : w ∈ (extChartAt 𝓘(ℂ, ℂ) v).source) :
    deriv (extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm)
      (extChartAt 𝓘(ℂ, ℂ) w w) ≠ 0 := by
  let τ := extChartAt 𝓘(ℂ, ℂ) v ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm
  let σ := extChartAt 𝓘(ℂ, ℂ) w ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm
  let c := extChartAt 𝓘(ℂ, ℂ) w w
  have hτc : τ c = extChartAt 𝓘(ℂ, ℂ) v w := by
    simp only [τ, c, Function.comp_apply, extChartAt_to_inv]
  have hτa : AnalyticAt ℂ τ c :=
    analyticAt_original_chart_transition v w (mem_extChartAt_target w)
      (by rwa [extChartAt_to_inv])
  have hσa : AnalyticAt ℂ σ (τ c) := by
    rw [hτc]
    exact analyticAt_original_chart_transition w v ((extChartAt 𝓘(ℂ, ℂ) v).map_source hw)
      (by rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hw]; exact mem_extChartAt_source w)
  have hid : (σ ∘ τ) =ᶠ[𝓝 c] id := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ (extChartAt 𝓘(ℂ, ℂ) w).target :=
      extChartAt_target_mem_nhds w
    have h2 : ∀ᶠ z in 𝓝 c,
        (extChartAt 𝓘(ℂ, ℂ) w).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) v).source := by
      apply (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds
      rw [extChartAt_to_inv]
      exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) v).mem_nhds hw
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [σ, τ, Function.comp_apply, id_eq]
    rw [(extChartAt 𝓘(ℂ, ℂ) v).left_inv hz2, (extChartAt 𝓘(ℂ, ℂ) w).right_inv hz1]
  have hd := hσa.differentiableAt.hasDerivAt.comp c hτa.differentiableAt.hasDerivAt
  have hone : deriv σ (τ c) * deriv τ c = 1 := by
    rw [← (hd.congr_of_eventuallyEq hid.symm).deriv, deriv_id]
  exact right_ne_zero_of_mul_eq_one hone

end
end Dubon2026.SourceFunctionField.OriginalChart
