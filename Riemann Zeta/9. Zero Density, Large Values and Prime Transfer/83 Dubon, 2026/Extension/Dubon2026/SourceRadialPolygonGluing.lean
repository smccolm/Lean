import Dubon2026.SourceRadialPolygonState

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

theorem state_step (hvert : Function.Injective 𝒟.vert) {𝒯s : Finset 𝒟.ιE}
    (hT : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s)
    {𝒞 : Finset 𝒟.ιC} {G : Finset 𝒟.ιE} {ws : List (𝒟.ιE × Bool)} (hS : State 𝒟 𝒯s 𝒞 G ws)
    (h𝒞 : 𝒞 ≠ Finset.univ) :
    ∃ (𝒞' : Finset 𝒟.ιC) (G' : Finset 𝒟.ιE) (ws' : List (𝒟.ιE × Bool)),
      State 𝒟 𝒯s 𝒞' G' ws' ∧ 𝒞'.card = 𝒞.card + 1 := by
  classical

  have h𝒞ne : 𝒞.Nonempty := Finset.card_pos.1 (by have := hS.hcard; omega)
  obtain ⟨Cin, hCin⟩ := h𝒞ne
  obtain ⟨Cout, hCout⟩ : ∃ D, D ∉ 𝒞 := by
    by_contra hall
    push Not at hall
    exact h𝒞 (Finset.eq_univ_of_forall hall)

  obtain ⟨g, hg𝒯s, hcross⟩ := exists_crossing _ _ hT hCin hCout
  obtain ⟨σ, hin, hout⟩ : ∃ σ : Bool, Cside 𝒟 g σ ∈ 𝒞 ∧ Cside 𝒟 g (!σ) ∉ 𝒞 := by
    by_cases ht : Cside 𝒟 g true ∈ 𝒞
    · exact ⟨true, ht, fun hf => hcross ⟨fun _ => hf, fun _ => ht⟩⟩
    · refine ⟨false, ?_, ht⟩
      by_contra hf
      exact hcross ⟨fun h => absurd h ht, fun h => absurd h hf⟩

  have hgG : g ∉ G := by
    intro hgG
    obtain ⟨h1, h2⟩ := hS.hGin g hgG
    cases σ
    · exact hout h1
    · exact hout h2
  have hboth : Cside 𝒟 g true ∈ insert (Cside 𝒟 g (!σ)) 𝒞 ∧
      Cside 𝒟 g false ∈ insert (Cside 𝒟 g (!σ)) 𝒞 := by
    cases σ
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hin⟩
    · exact ⟨Finset.mem_insert_of_mem hin, Finset.mem_insert_self _ _⟩
  have hq_in : ∀ q : 𝒟.ιE × Bool, q.1 = g → Cs 𝒟 q ∈ 𝒞 → q = (g, σ) := by
    intro q hq1 hq
    obtain ⟨q₁, q₂⟩ := q
    simp only at hq1
    subst hq1
    by_cases h : q₂ = σ
    · rw [h]
    · exfalso
      have hq₂ : q₂ = !σ := by cases σ <;> cases q₂ <;> simp_all
      rw [hq₂] at hq
      exact hout hq
  have hq_out : ∀ q : 𝒟.ιE × Bool, q.1 = g → Cs 𝒟 q = Cside 𝒟 g (!σ) → q = (g, !σ) := by
    intro q hq1 hq
    obtain ⟨q₁, q₂⟩ := q
    simp only at hq1
    subst hq1
    by_cases h : q₂ = !σ
    · rw [h]
    · exfalso
      have hq₂ : q₂ = σ := by cases σ <;> cases q₂ <;> simp_all
      rw [hq₂] at hq
      exact hout (by rw [← hq]; exact hin)
  set a : 𝒟.ιE × Bool := (g, σ) with ha_def
  set b : 𝒟.ιE × Bool := (g, !σ) with hb_def
  set C' : 𝒟.ιC := Cside 𝒟 g (!σ) with hC'_def
  have hC'𝒞 : C' ∉ 𝒞 := hout
  have ha_ws : a ∈ ws := (hS.hmem a).2 ⟨hin, hgG⟩
  have hb_arcs : b ∈ arcs 𝒟 C' := (mem_arcs 𝒟 C' b).2 rfl

  obtain ⟨n₁, l₁, hrot₁⟩ := exists_rotate_cons ha_ws
  obtain ⟨n₂, l₂, hrot₂⟩ := exists_rotate_cons hb_arcs
  have hnd₁ : (a :: l₁).Nodup := hrot₁ ▸ List.nodup_rotate.2 hS.hnd
  have hnd₂ : (b :: l₂).Nodup := hrot₂ ▸ List.nodup_rotate.2 (arcs_nodup 𝒟 C')
  have hmem₁ : ∀ q, q ∈ l₁ ↔ (q ∈ ws ∧ q ≠ a) := by
    intro q
    have h := (List.mem_rotate (l := ws) (a := q) (n := n₁))
    rw [hrot₁, List.mem_cons] at h
    rw [← h]
    constructor
    · intro hq
      exact ⟨Or.inr hq, fun hqa => (List.nodup_cons.1 hnd₁).1 (hqa ▸ hq)⟩
    · rintro ⟨hqa | hq, hne⟩
      · exact absurd hqa hne
      · exact hq
  have hmem₂ : ∀ q, q ∈ l₂ ↔ (Cs 𝒟 q = C' ∧ q ≠ b) := by
    intro q
    have h := (List.mem_rotate (l := arcs 𝒟 C') (a := q) (n := n₂))
    rw [hrot₂, List.mem_cons, mem_arcs] at h
    rw [← h]
    constructor
    · intro hq
      exact ⟨Or.inr hq, fun hqb => (List.nodup_cons.1 hnd₂).1 (hqb ▸ hq)⟩
    · rintro ⟨hqb | hq, hne⟩
      · exact absurd hqb hne
      · exact hq
  have hcyc₁ : Cyc (Corner 𝒟 G) (a :: l₁) := hrot₁ ▸ cyc_rotate n₁ hS.hcyc
  have hcyc₂ : Cyc (Corner 𝒟 G) (b :: l₂) := hrot₂ ▸ cyc_rotate n₂ (cyc_arcs 𝒟 hvert G C')
  have hGG' : G ⊆ insert g G := Finset.subset_insert g G
  have hg' : g ∈ insert g G := Finset.mem_insert_self g G
  refine ⟨insert C' 𝒞, insert g G, l₁ ++ l₂, ?_, Finset.card_insert_of_notMem hC'𝒞⟩
  refine
    { hG := Finset.insert_subset hg𝒯s hS.hG
      hGin := ?_
      hcard := by
        have := hS.hcard
        rw [Finset.card_insert_of_notMem hgG, Finset.card_insert_of_notMem hC'𝒞]; omega
      hnd := ?_
      hmem := ?_
      hcyc := ?_ }
  · intro g' hg'
    rcases Finset.mem_insert.1 hg' with rfl | hg'G
    · cases σ
      · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hin⟩
      · exact ⟨Finset.mem_insert_of_mem hin, Finset.mem_insert_self _ _⟩
    · obtain ⟨h1, h2⟩ := hS.hGin g' hg'G
      exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
  · refine List.Nodup.append (List.nodup_cons.1 hnd₁).2 (List.nodup_cons.1 hnd₂).2 ?_
    intro q hq₁ hq₂
    have hq₁' := ((hS.hmem q).1 ((hmem₁ q).1 hq₁).1).1
    have hq₂' := ((hmem₂ q).1 hq₂).1
    exact hC'𝒞 (hq₂' ▸ hq₁')
  · intro q
    rw [List.mem_append, hmem₁, hmem₂, hS.hmem, Finset.mem_insert, Finset.mem_insert]
    constructor
    · rintro (⟨⟨hq𝒞, hqG⟩, hqa⟩ | ⟨hqC', hqb⟩)
      · refine ⟨Or.inr hq𝒞, ?_⟩
        rintro (hqg | hqG')
        · exact hqa (hq_in q hqg hq𝒞)
        · exact hqG hqG'
      · refine ⟨Or.inl hqC', ?_⟩
        rintro (hqg | hqG')
        · exact hqb (hq_out q hqg hqC')
        · exfalso
          have h2 := hS.hGin q.1 hqG'
          have hCs : Cs 𝒟 q ∈ 𝒞 := by
            obtain ⟨q₁, q₂⟩ := q
            cases q₂
            · exact h2.2
            · exact h2.1
          rw [hqC'] at hCs
          exact hC'𝒞 hCs
    · rintro ⟨hq𝒞, hqG'⟩
      have hqg : q.1 ≠ g := fun h => hqG' (Or.inl h)
      have hqG : q.1 ∉ G := fun h => hqG' (Or.inr h)
      rcases hq𝒞 with hqC' | hq𝒞
      · exact Or.inr ⟨hqC', fun h => hqg (by rw [h])⟩
      · exact Or.inl ⟨⟨hq𝒞, hqG⟩, fun h => hqg (by rw [h])⟩
  · refine cyc_splice hcyc₁ hcyc₂ (fun x y h => corner_mono 𝒟 hGG' h) ?_ ?_
    · intro x y hxa hby
      exact corner_junction 𝒟 hGG' hg' σ hxa hby
    · intro x y hxb hay
      have hay' : Corner 𝒟 G (g, !(!σ)) y := by rw [Bool.not_not]; exact hay
      exact corner_junction 𝒟 hGG' hg' (!σ) hxb hay'

theorem state_final (hvert : Function.Injective 𝒟.vert) {𝒯s : Finset 𝒟.ιE}
    (hT : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s) :
    ∀ (n : ℕ) (𝒞 : Finset 𝒟.ιC) (G : Finset 𝒟.ιE) (ws : List (𝒟.ιE × Bool)),
      State 𝒟 𝒯s 𝒞 G ws → 𝒞.card + n = Fintype.card 𝒟.ιC →
      ∃ (G : Finset 𝒟.ιE) (ws : List (𝒟.ιE × Bool)), State 𝒟 𝒯s Finset.univ G ws
  | 0, 𝒞, G, ws, hS, hn => by
    have h𝒞 : 𝒞 = Finset.univ := Finset.eq_univ_of_card 𝒞 (by simpa using hn)
    exact ⟨G, ws, h𝒞 ▸ hS⟩
  | n + 1, 𝒞, G, ws, hS, hn => by
    have h𝒞 : 𝒞 ≠ Finset.univ := by
      rintro rfl
      rw [Finset.card_univ] at hn
      omega
    obtain ⟨𝒞', G', ws', hS', hcard'⟩ := state_step 𝒟 hvert hT hS h𝒞
    exact state_final hvert hT n 𝒞' G' ws' hS' (by omega)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
