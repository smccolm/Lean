import Dubon2026.SourceRadialCycleChainIdentification

/-! DUB-17/18 -> original Abel-Jacobi -> actual cycle periods.
Realize each integer fundamental cycle by a loop on the actual skeleton and
prove its integral for every complex functional satisfying the elementary
skeleton laws. The loop is chosen before the functional, as required for period generation and raw
reciprocity. Adapted from the verified Apache-2.0 source
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
noncomputable section
open SourceCurve Set IntegerEdgeChains RadialDissectionTrees
variable {X : Type*} [TopologicalSpace X]

theorem exists_fundamental_cycle_loop (D : RadialCellDissection X) {T : Finset D.ιE}
    {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ j w, (∑ e with (D.ends e).2 = w, Z j e) =
      ∑ e with (D.ends e).1 = w, Z j e)
    (hdelta : ∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0)
    (hzero : ∀ j ∈ T, Z j = 0)
    (hT : IsTree (hdΓ D) (tlΓ D) T) (hw : IsWalkConn (hdΓ D) (tlΓ D) T)
    (j : D.ιE) :
    ∃ γ : Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
      (∀ t, γ t ∈ D.skeleton) ∧
      ∀ (I : {P Q : X} → Path P Q → ℂ), SkeletonIntegral D @I →
        I γ = ∑ e, (Z j e : ℂ) * I (edgePath D e) := by
  classical
  by_cases hj : j ∈ T
  · refine ⟨Path.refl _, fun _ => (vert_mem_skeleton D j).1, fun I hI => ?_⟩
    simp only [hzero j hj, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    exact hI.refl _ (vert_mem_skeleton D j).1
  · obtain ⟨p, c, hps, hcT, hbd, hint⟩ := exists_path_of_walk D T
      (vert_mem_skeleton D j).2 (endpoint_walk_of_integer_walk D hw (D.ends j).2 (D.ends j).1)
    have hZj := cycle_eq_edge_add_return_chain D hZ hdelta hT hj hcT hbd
    refine ⟨(edgePath D j).trans p, mem_skeleton_trans D (edgePath_mem_skeleton D j) hps,
      fun I hI => ?_⟩
    have hp := hint @I hI
    rw [hI.trans _ _ (edgePath_mem_skeleton D j) hps, hp, hZj]
    have hs : ∀ e, (((if e = j then 1 else 0) + c e : ℤ) : ℂ) * I (edgePath D e) =
        (if e = j then I (edgePath D e) else 0) + (c e : ℂ) * I (edgePath D e) := by
      intro e; split_ifs <;> push_cast <;> ring
    simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
