import Dubon2026.SourceRadialDissectionTreeCotree
import Dubon2026.SourceCellCyclicBoundaryWords
import Dubon2026.SourceCellIntegerTreeCut

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

/-- Actual cell of an oriented edge letter. -/
noncomputable abbrev Cs (q : 𝒟.ιE × Bool) : 𝒟.ιC := Cside 𝒟 q.1 q.2

/-- Initial vertex of an oriented edge letter. -/
abbrev sV (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

/-- Terminal vertex of an oriented edge letter. -/
abbrev eV (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

theorem eV_not (g : 𝒟.ιE) (σ : Bool) : eV 𝒟 (g, !σ) = sV 𝒟 (g, σ) := by
  cases σ <;> rfl

theorem sV_mem_ends (g : 𝒟.ιE) (σ : Bool) :
    sV 𝒟 (g, σ) = (𝒟.ends g).1 ∨ sV 𝒟 (g, σ) = (𝒟.ends g).2 := by
  cases σ <;> simp [sV]

theorem Cs_side (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) : Cs 𝒟 (𝒟.side C k) = C :=
  (Cside_eq_iff 𝒟 _ _ C).2 ⟨k, rfl⟩

theorem side_injective (C : 𝒟.ιC) : Function.Injective (𝒟.side C) := by
  intro k k' hkk'
  have := 𝒟.side_bij.injective (a₁ := ⟨C, k⟩) (a₂ := ⟨C, k'⟩) hkk'
  exact (Sigma.mk.inj_iff.1 this).2.eq

theorem corner_arc (hvert : Function.Injective 𝒟.vert) (C : 𝒟.ιC)
    (k : Fin (𝒟.cell C).R.N) : eV 𝒟 (𝒟.side C k) = sV 𝒟 (𝒟.side C (nxt k)) := by
  apply hvert
  have h1 := (𝒟.arc_ends C k).2
  have h2 := (𝒟.arc_ends C (nxt k)).1
  have hb : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.succ) =
      (𝒟.cell C).bdry ((𝒟.cell C).R.φs (nxt k).castSucc) := by
    by_cases hk : k.val + 1 < (𝒟.cell C).R.N
    · rw [show (nxt k).castSucc = k.succ from Fin.ext (by simp [nxt, hk])]
    · have h0 : (nxt k).castSucc = (0 : Fin _) := Fin.ext (by simp [nxt, hk])
      have hl : k.succ = Fin.last _ := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN,
        show (2 * π : ℝ) = 0 + 2 * π from by ring, cell_bdry_periodic]
  simp only [eV, sV]
  rw [← h1, ← h2, hb]

/-- Crossing a chosen cotree edge at the specified actual vertex. -/
def crossAt (G : Finset 𝒟.ιE) (v : 𝒟.ιV) (D D' : 𝒟.ιC) : Prop :=
  ∃ g ∈ G, ((Cside 𝒟 g true = D ∧ Cside 𝒟 g false = D') ∨
      (Cside 𝒟 g true = D' ∧ Cside 𝒟 g false = D)) ∧
    (v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2)

/-- Matching vertices and a cotree crossing chain between the adjacent letters. -/
def Corner (G : Finset 𝒟.ιE) (x y : 𝒟.ιE × Bool) : Prop :=
  eV 𝒟 x = sV 𝒟 y ∧ Relation.ReflTransGen (crossAt 𝒟 G (eV 𝒟 x)) (Cs 𝒟 x) (Cs 𝒟 y)

theorem crossAt_mono {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') (v : 𝒟.ιV) {D D' : 𝒟.ιC}
    (h : crossAt 𝒟 G v D D') : crossAt 𝒟 G' v D D' := by
  obtain ⟨g, hg, hside, hv⟩ := h
  exact ⟨g, hGG' hg, hside, hv⟩

theorem corner_mono {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') {x y : 𝒟.ιE × Bool}
    (h : Corner 𝒟 G x y) : Corner 𝒟 G' x y :=
  ⟨h.1, Relation.ReflTransGen.mono (fun {_ _} hDD' => crossAt_mono 𝒟 hGG' _ hDD') h.2⟩

theorem crossAt_pair {G : Finset 𝒟.ιE} {g : 𝒟.ιE} (hg : g ∈ G) (σ : Bool) {v : 𝒟.ιV}
    (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) :
    crossAt 𝒟 G v (Cs 𝒟 (g, σ)) (Cs 𝒟 (g, !σ)) := by
  refine ⟨g, hg, ?_, hv⟩
  cases σ
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem corner_junction {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') {g : 𝒟.ιE} (hg : g ∈ G')
    (σ : Bool) {x y : 𝒟.ιE × Bool} (h₁ : Corner 𝒟 G' x (g, σ)) (h₂ : Corner 𝒟 G (g, !σ) y) :
    Corner 𝒟 G' x y := by
  obtain ⟨hv₁, hl₁⟩ := h₁
  obtain ⟨hv₂, hl₂⟩ := h₂
  have hvx : eV 𝒟 (g, !σ) = eV 𝒟 x := by rw [eV_not, hv₁]
  refine ⟨?_, ?_⟩
  · rw [← hv₂, hvx]
  · rw [hvx] at hl₂
    refine hl₁.trans (Relation.ReflTransGen.head ?_
      (Relation.ReflTransGen.mono (fun {_ _} hDD' => crossAt_mono 𝒟 hGG' _ hDD') hl₂))
    refine crossAt_pair 𝒟 hg σ ?_
    rw [hv₁]; exact sV_mem_ends 𝒟 g σ

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
