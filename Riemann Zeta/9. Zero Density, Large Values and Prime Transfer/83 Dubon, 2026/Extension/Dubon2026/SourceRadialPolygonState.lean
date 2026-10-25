import Dubon2026.SourceRadialPolygonCorners
import Mathlib.Data.List.OfFn

/-! DUB-17/18 -> actual cover Abel-Jacobi -> raw reciprocity -> polygon word.
Join actual analytic cells across the dual tree, retaining labeled oriented
edges, actual cover vertex corners and cotree paths. Integer tree lemmas and
radial endpoint facts are reused from the preceding proved construction.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
noncomputable section
open SourceCurve Set Real IntegerEdgeChains RadialDissectionTrees CyclicBoundaryWords
open DissectionTrees (nxt nxt_val)
variable {X : Type*} [TopologicalSpace X] (𝒟 : RadialCellDissection X)

/-- Cyclically ordered actual boundary letters of one analytic cell. -/
noncomputable def arcs (C : 𝒟.ιC) : List (𝒟.ιE × Bool) :=
  List.ofFn (fun k : Fin (𝒟.cell C).R.N => 𝒟.side C k)

theorem mem_arcs (C : 𝒟.ιC) (q : 𝒟.ιE × Bool) : q ∈ arcs 𝒟 C ↔ Cs 𝒟 q = C := by
  rw [arcs, List.mem_ofFn, Cs, Cside_eq_iff]

theorem arcs_nodup (C : 𝒟.ιC) : (arcs 𝒟 C).Nodup := by
  rw [arcs, List.nodup_ofFn]
  exact side_injective 𝒟 C

theorem cyc_arcs (hvert : Function.Injective 𝒟.vert) (G : Finset 𝒟.ιE) (C : 𝒟.ιC) :
    Cyc (Corner 𝒟 G) (arcs 𝒟 C) := by
  refine cyc_of_getElem (fun k hk => ?_)
  have hlen : (arcs 𝒟 C).length = (𝒟.cell C).R.N := by simp [arcs]
  have hk' : k < (𝒟.cell C).R.N := hlen ▸ hk
  have h1 : (arcs 𝒟 C)[k] = 𝒟.side C ⟨k, hk'⟩ := by simp [arcs]
  have h2 : (arcs 𝒟 C)[(k + 1) % (arcs 𝒟 C).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)) =
      𝒟.side C (nxt ⟨k, hk'⟩) := by
    simp only [arcs, List.getElem_ofFn, List.length_ofFn]
    congr 1
    exact Fin.ext (by simp [nxt_val])
  rw [h1, h2]
  refine ⟨corner_arc 𝒟 hvert C _, ?_⟩
  rw [Cs_side, Cs_side]

/-- Finite cell-gluing invariant for the actual boundary polygon. -/
structure State (𝒯s : Finset 𝒟.ιE) (𝒞 : Finset 𝒟.ιC) (G : Finset 𝒟.ιE)
    (ws : List (𝒟.ιE × Bool)) : Prop where
  hG : G ⊆ 𝒯s
  hGin : ∀ g ∈ G, Cside 𝒟 g true ∈ 𝒞 ∧ Cside 𝒟 g false ∈ 𝒞
  hcard : G.card + 1 = 𝒞.card
  hnd : ws.Nodup
  hmem : ∀ q : 𝒟.ιE × Bool, q ∈ ws ↔ (Cs 𝒟 q ∈ 𝒞 ∧ q.1 ∉ G)
  hcyc : Cyc (Corner 𝒟 G) ws

theorem state_init (hvert : Function.Injective 𝒟.vert) (𝒯s : Finset 𝒟.ιE) (C₀ : 𝒟.ιC) :
    State 𝒟 𝒯s {C₀} ∅ (arcs 𝒟 C₀) where
  hG := Finset.empty_subset _
  hGin := fun g hg => absurd hg (Finset.notMem_empty g)
  hcard := by simp
  hnd := arcs_nodup 𝒟 C₀
  hmem := fun q => by simp [mem_arcs]
  hcyc := cyc_arcs 𝒟 hvert ∅ C₀

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
