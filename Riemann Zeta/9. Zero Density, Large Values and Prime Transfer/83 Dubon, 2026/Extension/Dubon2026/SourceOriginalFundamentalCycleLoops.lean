import Dubon2026.SourceOriginalCycleChainIdentification

/-! DUB-17/18 -> original Abel-Jacobi -> actual cycle periods.
Realize each integer fundamental cycle by a loop on the actual skeleton and
prove its integral for every original differential regular there. The loop is
chosen before the differential, as required for period generation and raw
reciprocity. Adapted from the verified Apache-2.0 source
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart IntegerEdgeChains DissectionTrees
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_fundamental_cycle_loop (D : CellDissection N) {T : Finset D.ιE}
    {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ j w, (∑ e with (D.ends e).2 = w, Z j e) =
      ∑ e with (D.ends e).1 = w, Z j e)
    (hdelta : ∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0)
    (hzero : ∀ j ∈ T, Z j = 0)
    (hT : IsTree (hdΓ D) (tlΓ D) T) (hw : IsWalkConn (hdΓ D) (tlΓ D) T)
    (j : D.ιE) :
    ∃ γ : Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
      (∀ t, γ t ∈ D.skeleton) ∧
      ∀ θ : Ω[F⁄ℂ], RegOnSkeleton D θ →
        (∃ g, IsPrimitiveAlong N θ γ g) ∧
          pathIntegral N θ γ = ∑ e, (Z j e : ℂ) * D.edgeInt θ e := by
  classical
  by_cases hj : j ∈ T
  · refine ⟨Path.refl _, fun _ => (vert_mem_skeleton D j).1, fun θ hθ => ?_⟩
    have hr : ∀ t, ((Path.refl (D.vert (D.ends j).1)) t).differentialCoeff θ ∈
        ((Path.refl (D.vert (D.ends j).1)) t).toValuationSubring :=
      fun _ => (D.vert (D.ends j).1).mem_of_ord_nonneg (hθ _ (vert_mem_skeleton D j).1)
    have he := pathIntegral_symm_of_coeff_mem N (Path.refl (D.vert (D.ends j).1)) hr
    change pathIntegral N θ (Path.refl (D.vert (D.ends j).1)) =
      -pathIntegral N θ (Path.refl (D.vert (D.ends j).1)) at he
    refine ⟨primitive_on_skeleton D hθ (fun _ => (vert_mem_skeleton D j).1), ?_⟩
    simp only [hzero j hj, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    linear_combination (1 / 2 : ℂ) * he
  · obtain ⟨p, c, hps, hcT, hbd, hint⟩ := exists_path_of_walk D T
      (vert_mem_skeleton D j).2 (endpoint_walk_of_integer_walk D hw (D.ends j).2 (D.ends j).1)
    have hZj := cycle_eq_edge_add_return_chain D hZ hdelta hT hj hcT hbd
    refine ⟨(edgePath D j).trans p, mem_skeleton_trans D (edgePath_mem_skeleton D j) hps,
      fun θ hθ => ?_⟩
    obtain ⟨_, he⟩ := pathIntegral_edgePath D j (θ := θ) fun s hs =>
      hθ _ (mem_iUnion.2 ⟨D.arcOf (j, true), _, ⟨s, hs, rfl⟩, rfl⟩)
    obtain ⟨_, hp⟩ := hint θ hθ
    refine ⟨primitive_on_skeleton D hθ (mem_skeleton_trans D (edgePath_mem_skeleton D j) hps), ?_⟩
    rw [pathIntegral_trans_on_skeleton D _ _ hθ (edgePath_mem_skeleton D j) hps, he, hp, hZj]
    have hs : ∀ e, (((if e = j then 1 else 0) + c e : ℤ) : ℂ) * D.edgeInt θ e =
        (if e = j then D.edgeInt θ e else 0) + (c e : ℂ) * D.edgeInt θ e := by
      intro e; split_ifs <;> push_cast <;> ring
    simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
