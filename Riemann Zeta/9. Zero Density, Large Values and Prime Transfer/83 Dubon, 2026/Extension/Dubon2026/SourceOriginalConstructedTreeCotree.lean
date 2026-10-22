import Dubon2026.SourceOriginalDissectionTreeCotree

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops.
The constructed original dissection discharges vertex injectivity, incidence
and Euler in the tree/cotree theorem. Thus arbitrary marked original places
have disjoint actual primal and dual trees with exactly 2g remaining edges.
Realizing and generating analytic loop integrals remains to be proved.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem OriginalGlobalCellCover.tree_cotree {Marked : Finset ℂ}
    (A : OriginalGlobalCellCover N Marked) :
    ∃ T Ts : Finset A.dissection.ιE,
      IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
      Disjoint T Ts ∧
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
      IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T := by
  haveI : Nonempty A.dissection.ιC := by
    obtain ⟨P⟩ := nonempty_original_places N ℂ
    obtain ⟨i, _⟩ := A.covers P
    exact ⟨i⟩
  obtain ⟨T, Ts, ht, hts, hd, hc, hw⟩ := exists_tree_cotree A.dissection
    CellPairing.vertex_injective A.pairing.vertex_incident A.dissection_euler_identity
  refine ⟨T, Ts, ht, hts, hd, hc, ?_⟩
  intro u v
  refine Relation.ReflTransGen.mono (fun {a b} ⟨e, he, hab⟩ => ⟨e, he, ?_⟩) (hw u v)
  rcases hab with hab | hab
  · exact Or.inr ⟨congrArg Prod.snd hab, congrArg Prod.fst hab⟩
  · exact Or.inl ⟨congrArg Prod.snd hab, congrArg Prod.fst hab⟩

theorem exists_original_centered_tree_cotree (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      ∃ T Ts : Finset A.dissection.ιE,
        IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
        IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
        Disjoint T Ts ∧
        (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
        IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T := by
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  exact ⟨Marked, A, hcent, hsep, A.tree_cotree⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
