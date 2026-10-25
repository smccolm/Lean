import Dubon2026.SourceRadialTreeWalkIntegrals
import Dubon2026.SourceRadialFundamentalCycleSystem

/-! DUB-17/18 -> original Abel-Jacobi -> actual fundamental-cycle loops.
The unique integer chain in the actual primal tree identifies the return walk
with the already constructed fundamental cycle. Reuse of the proved boundary
algebra avoids a second filtered-sum cancellation argument.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
noncomputable section
open SourceCurve Set IntegerEdgeChains RadialDissectionTrees
variable {X : Type*} [TopologicalSpace X]

theorem cycle_eq_edge_add_return_chain (D : RadialCellDissection X) {T : Finset D.ιE}
    {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ j w, (∑ e with (D.ends e).2 = w, Z j e) =
      ∑ e with (D.ends e).1 = w, Z j e)
    (hdelta : ∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0)
    (hT : IsTree (hdΓ D) (tlΓ D) T)
    {j : D.ιE} (hj : j ∉ T) {c : D.ιE → ℤ} (hc : ∀ e ∉ T, c e = 0)
    (hb : ∀ w, bd (hdΓ D) (tlΓ D) c w =
      (if w = (D.ends j).1 then 1 else 0) - (if w = (D.ends j).2 then 1 else 0)) :
    Z j = fun e => (if e = j then 1 else 0) + c e := by
  classical
  obtain ⟨c₀, _, hu⟩ := hT (D.ends j).2 (D.ends j).1
  have hc₀ := hu c ⟨hc, hb⟩
  have hz₀ : (Z j - fun e => if e = j then 1 else 0) = c₀ := by
    apply hu
    constructor
    · intro e he
      simp only [Pi.sub_apply, hdelta j (Finset.mem_compl.mpr hj) e (Finset.mem_compl.mpr he)]
      simp only [eq_comm (a := j), sub_self]
    · intro w
      have hz : bd (hdΓ D) (tlΓ D) (Z j) w = 0 := sub_eq_zero.mpr (hZ j w)
      rw [bd_sub, hz, bd_single]
      simp only [hdΓ, tlΓ]
      ring
  funext e
  have he := congrFun (hz₀.trans hc₀.symm) e
  simp only [Pi.sub_apply] at he
  linarith

theorem endpoint_walk_of_integer_walk (D : RadialCellDissection X) {T : Finset D.ιE}
    (hw : IsWalkConn (hdΓ D) (tlΓ D) T) (u v : D.ιV) :
    Relation.ReflTransGen
      (fun a b : D.ιV => ∃ e ∈ T, D.ends e = (a, b) ∨ D.ends e = (b, a)) u v := by
  apply Relation.ReflTransGen.mono (fun {a b} h => ?_) (hw u v)
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr (Prod.ext h.2 h.1)⟩
  · exact ⟨e, he, Or.inl (Prod.ext h.2 h.1)⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
