import Dubon2026.SourceOriginalChartNeighborhoods

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual
upper-half-plane path integrals. The existing normalized ramified family
has the same local orders as an original chart, so the proved branch
comparison identifies it with the chart near its center. This supplies
continuity without assuming it for the choice of a complex root.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem originalRamifiedPlace_continuousAt_zero (τ : ℍ) :
    ContinuousAt (originalRamifiedPlace N τ) (0 : ℂ) := by
  obtain ⟨δ, hδ, ho⟩ := originalRamifiedPlace_chart_orders N τ
  let v := originalAnalyticPlace N τ
  let S : ComparisonData N :=
    { γ := placeFamily N v
      γ' := originalRamifiedPlace N τ
      v := v
      U := ball 0 (placeRadius N v)
      U' := ball 0 δ
      z₀ := 0
      z₀' := 0
      hU := ball_mem_nhds 0 (place_spec N v).1
      hU' := ball_mem_nhds 0 hδ
      h₀ := (originalRamifiedPlace_zero N τ).trans (place_spec N v).2.1.symm
      ht := (place_spec N v).2.2.2
      hγ := (place_spec N v).2.2.1
      hγ' := ho }
  have ht : ContinuousAt S.transition 0 := S.analyticAt_transition.continuousAt
  have hc : ContinuousAt (placeFamily N v) (S.transition 0) := by
    rw [S.transition_self]
    exact placeFamily_continuousAt_zero N v
  exact (hc.comp ht).congr (S.eventually_place_eq.mono fun _ h => h.symm)

end
end Dubon2026.SourceFunctionField.OriginalChart
