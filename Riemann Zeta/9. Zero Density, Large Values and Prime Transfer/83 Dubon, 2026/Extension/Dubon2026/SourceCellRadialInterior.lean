import Dubon2026.SourceCellRadialNeighborhood
import Mathlib.Topology.Instances.Real.Lemmas

/-! DUB-17/18 -> raw geometric reciprocity -> cell dissection and primitive
domains. Native compactness of a continuous periodic range supplies a positive
lower radius. Continuity through the angle quotient proves the actual cell
interior is open, including at the center and across the argument branch cut.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
noncomputable section
open Set Complex Metric
open scoped Real

theorem exists_positive_lower_radius (R : RadialRegion) :
    ∃ m : ℝ, 0 < m ∧ ∀ φ, m ≤ R.r φ := by
  have hc := R.hper.compact_of_continuous (ne_of_gt Real.two_pi_pos) R.hcont
  obtain ⟨m, ⟨φ, rfl⟩, hm⟩ := hc.exists_isMinOn (Set.range_nonempty R.r) continuousOn_id
  exact ⟨R.r φ, R.hpos φ, fun t => hm ⟨t, rfl⟩⟩

theorem isOpen_Kint (R : RadialRegion) : IsOpen R.Kint := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ‖z - R.q‖ < R.r (arg (z - R.q)) := hz
  by_cases hzq : z = R.q
  · obtain ⟨m, hm, hmr⟩ := exists_positive_lower_radius R
    rw [hzq]
    refine Filter.mem_of_superset (ball_mem_nhds R.q hm) ?_
    intro w hw
    change ‖w - R.q‖ < R.r (arg (w - R.q))
    exact (show ‖w - R.q‖ < m from by simpa only [mem_ball, dist_eq_norm] using hw).trans_le
      (hmr (arg (w - R.q)))
  · have h0 : ContinuousAt (fun w : ℂ => w - R.q) z := continuousAt_id.sub continuousAt_const
    have hr0 : ContinuousAt (fun w : ℂ => R.r (arg w)) (z - R.q) :=
      continuousAt_periodic_radius_arg R.hcont R.hper (sub_ne_zero.mpr hzq)
    have hr : ContinuousAt (fun w : ℂ => R.r (arg (w - R.q))) z :=
      ContinuousAt.comp (f := fun w : ℂ => w - R.q) hr0 h0
    have hd := hr.sub h0.norm
    refine Filter.mem_of_superset (hd.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (sub_pos.mpr hz'))) ?_
    intro w hw
    have hw' : 0 < R.r (arg (w - R.q)) - ‖w - R.q‖ := hw
    exact sub_pos.mp hw'

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRegion
