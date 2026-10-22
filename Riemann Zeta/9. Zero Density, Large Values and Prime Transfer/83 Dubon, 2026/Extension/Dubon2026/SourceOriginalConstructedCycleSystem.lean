import Dubon2026.SourceCellIntegerFundamentalCycles
import Dubon2026.SourceOriginalConstructedPolygonWord

/-! DUB-17/18 -> original Abel-Jacobi -> actual period generators.
The same constructed original dissection, primal tree, dual tree and polygon
word now carry an integer fundamental-cycle system. Its universal additive
decomposition applies to the actual edge index and is ready for the analytic
loop realization and period/jump consumers; these remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees DissectionPolygon
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_centered_cycle_system (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked)
      (T Ts : Finset A.dissection.ιE) (Z : A.dissection.ιE → A.dissection.ιE → ℤ),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      IsTree (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      IsTree (fun e => Cside A.dissection e true) (fun e => Cside A.dissection e false) Ts ∧
      Disjoint T Ts ∧
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F) ∧
      IsWalkConn (hdΓ A.dissection) (tlΓ A.dissection) T ∧
      PolygonWordConclusion A.dissection Ts ∧
      (∀ j w, (∑ e with (A.dissection.ends e).2 = w, Z j e) =
        (∑ e with (A.dissection.ends e).1 = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {B : Type*} [AddCommGroup B] (f : A.dissection.ιE → B),
        (∀ w, (∑ e with (A.dissection.ends e).2 = w, f e) =
          (∑ e with (A.dissection.ends e).1 = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  obtain ⟨Marked, A, _, hcent, hsep⟩ := exists_original_centered_global_cover N P₀ S
  obtain ⟨T, Ts, ht, hts, hd, hc, hw, hword⟩ := A.tree_cotree_polygon
  obtain ⟨Z, hz, hdelta, hzero, hdec⟩ := exists_fundamental_cycles
    (hdΓ A.dissection) (tlΓ A.dissection) T ht
  exact ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
