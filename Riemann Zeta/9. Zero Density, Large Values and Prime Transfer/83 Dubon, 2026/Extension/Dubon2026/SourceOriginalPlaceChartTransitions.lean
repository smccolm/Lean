import Dubon2026.SourceOriginalPlaceCharts

/-! DUB-17/18 -> original torsion cardinality -> global complex charts.
The existing uniformizer-division branch-uniqueness theorem applies
to every pair of the actual all-place charts. Their overlap domains
are open and their transition functions are analytic, including cusps.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable {N : ℕ} [NeZero N]
variable (v w : Place ℂ (modularFunctionFieldOver N ℂ))

theorem placeChart_trans_source :
    ((placeChart N v).symm.trans (placeChart N w)).source =
      {z | z ∈ Metric.ball 0 (placeRadius N v) ∧
        placeFamily N v z ∈ (placeChart N w).source} := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  rfl

private def overlapData (z z' : ℂ)
    (hz : z ∈ Metric.ball 0 (placeRadius N v))
    (hz' : z' ∈ Metric.ball 0 (placeRadius N w))
    (he : placeFamily N w z' = placeFamily N v z) : ComparisonData N where
  γ := placeFamily N w
  γ' := placeFamily N v
  v := w
  U := Metric.ball 0 (placeRadius N w)
  U' := Metric.ball 0 (placeRadius N v)
  z₀ := z'
  z₀' := z
  hU := Metric.isOpen_ball.mem_nhds hz'
  hU' := Metric.isOpen_ball.mem_nhds hz
  h₀ := he.symm
  ht := (place_spec N w).2.2.2
  hγ := (place_spec N w).2.2.1
  hγ' := (place_spec N v).2.2.1

theorem isOpen_placeChart_trans_source :
    IsOpen ((placeChart N v).symm.trans (placeChart N w)).source := by
  rw [placeChart_trans_source, isOpen_iff_mem_nhds]
  rintro z ⟨hz, z', hz', he⟩
  let S := overlapData v w z z' hz hz' he
  have hB := S.eventually_place_eq
  have hin : ∀ᶠ u in 𝓝 z, S.transition u ∈ Metric.ball 0 (placeRadius N w) :=
    S.tendsto_transition.eventually (Metric.isOpen_ball.mem_nhds hz')
  filter_upwards [hB, hin, Metric.isOpen_ball.mem_nhds hz] with u hu hu' hu''
  exact ⟨hu'', S.transition u, hu', hu.symm⟩

theorem analyticOnNhd_placeChart_transition :
    AnalyticOnNhd ℂ ((placeChart N v).symm.trans (placeChart N w))
      ((placeChart N v).symm.trans (placeChart N w)).source := by
  intro z hz
  rw [placeChart_trans_source] at hz
  obtain ⟨hz, z', hz', he⟩ := hz
  let S := overlapData v w z z' hz hz' he
  exact S.analyticAt_transition

end
end Dubon2026.SourceFunctionField.OriginalChart
