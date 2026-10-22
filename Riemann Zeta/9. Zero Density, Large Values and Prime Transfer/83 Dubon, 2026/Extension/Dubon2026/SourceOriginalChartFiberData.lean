import Dubon2026.SourceOriginalChartNeighborhoods

/-! DUB-17/18 -> original torsion cardinality -> compact original curve.
Expose exactly the existing chart facts needed by the finite-fiber cover:
injectivity, analytic evaluation, exact central order and a regular disk.
All are consequences of the proved original all-place chart package.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem placeFamily_injOn (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    InjOn (placeFamily N v) (ball 0 (placeRadius N v)) := by
  intro z hz u hu he
  have h := congrArg (fun w => originalPlaceEval N ℂ w v.uniformizer) he
  dsimp only at h
  rwa [place_eval_uniformizer N v hz, place_eval_uniformizer N v hu] at h

theorem analyticAt_place_reading (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {g : modularFunctionFieldOver N ℂ} (hg : g ∈ v.toValuationSubring) :
    AnalyticAt ℂ (fun u => originalPlaceEval N ℂ (placeFamily N v u) g) 0 := by
  apply (place_spec N v).2.2.1.analyticAt (mem_ball_self (place_spec N v).1)
  rwa [(place_spec N v).2.1]

theorem meromorphicOrderAt_place_reading (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {g : modularFunctionFieldOver N ℂ} (hg : g ≠ 0) :
    meromorphicOrderAt (fun u => originalPlaceEval N ℂ (placeFamily N v u) g) 0 = (v.ord g : WithTop ℤ) := by
  have h := ((place_spec N v).2.2.1 0 (mem_ball_self (place_spec N v).1) g hg).2.1
  rwa [(place_spec N v).2.1] at h

theorem exists_place_reading_regular_disk (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {g : modularFunctionFieldOver N ℂ} (hg : g ∈ v.toValuationSubring) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → g ∈ (placeFamily N v u).toValuationSubring := by
  have hm : g ∈ (placeFamily N v 0).toValuationSubring := by rwa [(place_spec N v).2.1]
  have he := (place_spec N v).2.2.1.eventually_mem (ball_mem_nhds 0 (place_spec N v).1) hm
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp he
  exact ⟨δ, hδ, fun u hu => h u (by simpa only [mem_ball, dist_zero_right] using hu)⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
