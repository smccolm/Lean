import Dubon2026.SourceMeromorphicOrderNeighborhoods

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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [T2Space M]

omit [ChartedSpace ℂ M] in
theorem eventually_nhdsWithin_compl_not_mem {S : Set (M)} (hS : S.Finite)
    (w : M) : ∀ᶠ u in 𝓝[≠] w, u ∉ S := by
  have hfin : (S \ {w}).Finite := hS.subset diff_subset
  have hopen : IsOpen (S \ {w})ᶜ := hfin.isClosed.isOpen_compl
  have hmem : w ∈ (S \ {w})ᶜ := fun h => h.2 rfl
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hopen.mem_nhds hmem] with u hu hne
  intro huS
  exact hu ⟨huS, hne⟩

omit [T2Space M] in
theorem eventually_pf_of_eventually_nhdsWithin {P : M → Prop} (w : M)
    (h : ∀ᶠ u in 𝓝[≠] w, P u) : ∀ᶠ z in (𝓝[≠] (ctr w)), P ((φ w).symm z) := by
  rw [eventually_nhdsWithin_iff] at h
  have h1 : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ≠ w → P ((φ w).symm z) := by
    have hc : ContinuousAt (φ w).symm (ctr w) := continuousAt_extChartAt_symm w
    have h' : ∀ᶠ u in 𝓝 ((φ w).symm (ctr w)), u ≠ w → P u := by
      rw [extChartAt_to_inv]; exact h
    exact hc.eventually h'
  have h2 : ∀ᶠ z in 𝓝 (ctr w), z ∈ (φ w).target := extChartAt_target_mem_nhds w
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2] with z hz hzt hne
  refine hz fun heq => hne ?_
  have : φ w ((φ w).symm z) = z := (φ w).right_inv hzt
  rw [mem_singleton_iff, ← this, heq]



end
end Dubon2026.SourceFunctionField.OriginalExpTopology
