import Dubon2026.SourceOriginalWeilCoverCharts
import Dubon2026.SourceCurveAnalyticChartBranchEquality

/-! DUB-17/18 -> auxiliary cover Abel comparison -> compatible actual charts.
The proved uniformizer-division branch equality applies to every overlap of
the literal cover charts. It gives open overlap domains and analytic
transition functions, without a supplied atlas or compatibility premise. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD
variable (v w : Place ℂ (Polynomial.SplittingField
  (X ^ n - C f : (modularFunctionFieldOver N ℂ)[X])))
include v w

theorem placeChart_trans_source :
    ((placeChart N n f D hf hfD v).symm.trans (placeChart N n f D hf hfD w)).source =
      {z | z ∈ Metric.ball 0 (placeRadius N n f D hf hfD v) ∧
        placeFamily N n f D hf hfD v z ∈ (placeChart N n f D hf hfD w).source} := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  rfl

private def overlapData (z z' : ℂ)
    (hz : z ∈ Metric.ball 0 (placeRadius N n f D hf hfD v))
    (hz' : z' ∈ Metric.ball 0 (placeRadius N n f D hf hfD w))
    (he : placeFamily N n f D hf hfD w z' = placeFamily N n f D hf hfD v z) : AnalyticChart.ComparisonData (originalWeilKummerCover_residue_bijective N ℂ n f) where
  γ := placeFamily N n f D hf hfD w
  γ' := placeFamily N n f D hf hfD v
  v := w
  U := Metric.ball 0 (placeRadius N n f D hf hfD w)
  U' := Metric.ball 0 (placeRadius N n f D hf hfD v)
  z₀ := z'
  z₀' := z
  hU := Metric.isOpen_ball.mem_nhds hz'
  hU' := Metric.isOpen_ball.mem_nhds hz
  h₀ := he.symm
  ht := (place_spec N n f D hf hfD w).2.2.2
  hγ := (place_spec N n f D hf hfD w).2.2.1
  hγ' := (place_spec N n f D hf hfD v).2.2.1

theorem isOpen_placeChart_trans_source :
    IsOpen ((placeChart N n f D hf hfD v).symm.trans (placeChart N n f D hf hfD w)).source := by
  rw [placeChart_trans_source, isOpen_iff_mem_nhds]
  rintro z ⟨hz, z', hz', he⟩
  let S := overlapData N n f D hf hfD v w z z' hz hz' he
  have hB := S.eventually_place_eq
  have hin : ∀ᶠ u in 𝓝 z, S.transition u ∈ Metric.ball 0 (placeRadius N n f D hf hfD w) :=
    S.tendsto_transition.eventually (Metric.isOpen_ball.mem_nhds hz')
  filter_upwards [hB, hin, Metric.isOpen_ball.mem_nhds hz] with u hu hu' hu''
  exact ⟨hu'', S.transition u, hu', hu.symm⟩

theorem analyticOnNhd_placeChart_transition :
    AnalyticOnNhd ℂ ((placeChart N n f D hf hfD v).symm.trans (placeChart N n f D hf hfD w))
      ((placeChart N n f D hf hfD v).symm.trans (placeChart N n f D hf hfD w)).source := by
  intro z hz
  rw [placeChart_trans_source] at hz
  obtain ⟨hz, z', hz', he⟩ := hz
  let S := overlapData N n f D hf hfD v w z z' hz hz' he
  exact S.analyticAt_transition

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
