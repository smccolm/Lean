import Dubon2026.SourceChartFiniteAvoidance
import Dubon2026.SourcePuncturedNeighborhoodConnected

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. Deleting finitely many points from the
connected original complex curve preserves path connectedness. Punctured
coordinate neighborhoods prevent a separation across a deleted point.
Adapted from S_AlgebraicCurve_exists_meromorphicOrderAt_eq_of_forall_pathIntegral_eq_two_pi_I_mul,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalExpTopology
noncomputable section
open Filter Topology Set Metric
open scoped Manifold ContDiff Topology

open MeromorphicCompact
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The part of a chart lying over its centered coordinate ball. -/
def disc (v : M) (r : ℝ) : Set (M) :=
  (φ v).source ∩ (φ v) ⁻¹' Metric.ball (ctr v) r

theorem isOpen_disc (v : M) (r : ℝ) : IsOpen (disc v r) :=
  isOpen_extChartAt_preimage' v Metric.isOpen_ball

theorem mem_disc (v : M) {r : ℝ} (hr : 0 < r) : v ∈ disc v r :=
  ⟨mem_extChartAt_source v, Metric.mem_ball_self hr⟩

theorem symm_mem_disc (v : M) {r : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (ctr v) r)
    (hzt : z ∈ (φ v).target) : (φ v).symm z ∈ disc v r := by
  refine ⟨(φ v).map_target hzt, ?_⟩
  show φ v ((φ v).symm z) ∈ Metric.ball (ctr v) r
  rw [(φ v).right_inv hzt]
  exact hz

theorem disc_eq_image (v : M) {r : ℝ} (hB : Metric.ball (ctr v) r ⊆ (φ v).target) :
    disc v r = (φ v).symm '' Metric.ball (ctr v) r :=
  ((φ v).symm_image_eq_source_inter_preimage hB).symm

theorem disc_diff_eq_image (v : M) {r : ℝ} (hB : Metric.ball (ctr v) r ⊆ (φ v).target) :
    disc v r \ {v} = (φ v).symm '' (Metric.ball (ctr v) r \ {ctr v}) := by
  ext x
  constructor
  · rintro ⟨⟨hxs, hxb⟩, hxv⟩
    refine ⟨φ v x, ⟨hxb, fun heq => hxv ?_⟩, (φ v).left_inv hxs⟩
    rw [mem_singleton_iff] at heq ⊢
    exact (φ v).injOn hxs (mem_extChartAt_source v) heq
  · rintro ⟨z, ⟨hzb, hzc⟩, rfl⟩
    refine ⟨symm_mem_disc v hzb (hB hzb), fun heq => hzc ?_⟩
    rw [mem_singleton_iff] at heq ⊢
    rw [← (φ v).right_inv (hB hzb), heq]

theorem isPathConnected_disc_diff (v : M) {r : ℝ} (hr : 0 < r)
    (hB : Metric.ball (ctr v) r ⊆ (φ v).target) : IsPathConnected (disc v r \ {v}) := by
  rw [disc_diff_eq_image v hB]
  exact (isPathConnected_ball_diff_singleton (ctr v) hr).image'
    ((continuousOn_extChartAt_symm v).mono (diff_subset.trans hB))

theorem isPathConnected_compl_of_finite [T2Space M] [ConnectedSpace M] {S : Set M}
    (hS : S.Finite) (hne : Sᶜ.Nonempty) : IsPathConnected Sᶜ := by
  haveI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace ℂ _
  refine (hS.isClosed.isOpen_compl.isConnected_iff_isPathConnected).1 ⟨hne, ?_⟩
  refine isPreconnected_compl_of_forall_nhd hS.isClosed fun s hs => ?_
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf s
    (eventually_pf_of_eventually_nhdsWithin (P := fun u => u ∉ S) s
      (eventually_nhdsWithin_compl_not_mem hS s))
  refine ⟨disc s r, isOpen_disc s r, mem_disc s hr, ?_, (isPathConnected_disc_diff s hr hB).isConnected.isPreconnected⟩
  rw [disc_diff_eq_image s hB]
  rintro - ⟨z, ⟨hzb, hzc⟩, rfl⟩
  exact hball z hzb hzc


end
end Dubon2026.SourceFunctionField.OriginalExpTopology
