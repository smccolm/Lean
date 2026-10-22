import Dubon2026.SourceOriginalComplexHausdorff

/-! DUB-17/18 -> original torsion cardinality -> compact complex curve.
Native Hausdorff separation and continuity of the actual inverse charts
give disjoint small parameter disks. These disks make the analytic
preimages at distinct original places distinct in the fiber-degree count.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem placeFamily_continuousAt_zero (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    letI := placeTopology N
    ContinuousAt (placeFamily N v) 0 := by
  letI := placeTopology N
  exact (continuousOn_placeFamily N v 0 (mem_ball_self (place_spec N v).1)).continuousAt
    (ball_mem_nhds 0 (place_spec N v).1)

theorem place_families_separated {v w : Place ℂ (modularFunctionFieldOver N ℂ)} (hne : v ≠ w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ z u : ℂ, ‖z‖ < δ → ‖u‖ < ε → placeFamily N v z ≠ placeFamily N w u := by
  letI := placeTopology N
  letI := place_t2Space N
  obtain ⟨U, V, hU, hV, hv, hw, hd⟩ := t2_separation hne
  have hcv := placeFamily_continuousAt_zero N v
  have hcw := placeFamily_continuousAt_zero N w
  rw [ContinuousAt, (place_spec N v).2.1] at hcv
  rw [ContinuousAt, (place_spec N w).2.1] at hcw
  obtain ⟨δ, hδ, hvδ⟩ := Metric.eventually_nhds_iff_ball.mp (hcv.eventually (hU.mem_nhds hv))
  obtain ⟨ε, hε, hwε⟩ := Metric.eventually_nhds_iff_ball.mp (hcw.eventually (hV.mem_nhds hw))
  refine ⟨δ, hδ, ε, hε, fun z u hz hu he => ?_⟩
  have hzU := hvδ z (by simpa only [mem_ball, dist_zero_right] using hz)
  have huV := hwε u (by simpa only [mem_ball, dist_zero_right] using hu)
  rw [he] at hzU
  exact Set.disjoint_left.mp hd hzU huV

end
end Dubon2026.SourceFunctionField.OriginalChart
