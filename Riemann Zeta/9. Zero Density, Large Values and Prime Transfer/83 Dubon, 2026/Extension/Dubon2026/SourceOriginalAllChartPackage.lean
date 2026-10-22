import Dubon2026.SourceOriginalAllPlaceParameters
import Dubon2026.SourceOriginalChartBranchEquality

/-! DUB-17/18 -> original torsion cardinality -> global complex charts.
The proved parameter at every actual original place supplies the exact
pointwise order inputs used by the existing branch-uniqueness theorem.
Thus finite-place transition arguments apply to cusp overlaps as well.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Topology

theorem original_place_parameter_package (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = v ∧ OriginalChart.Orders N γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, (γ z).ord
        (v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) z) = 1) := by
  obtain ⟨ρ, γ, hρ, h0, _, heval, ho⟩ := original_place_chart_parameter N v
  refine ⟨ρ, γ, hρ, h0, ho, ?_⟩
  intro z hz
  exact OriginalChart.Orders.uniformizer_sub_order ho (Metric.isOpen_ball.mem_nhds hz) v heval

end
end Dubon2026.SourceFunctionField
