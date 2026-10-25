import Dubon2026.SourceRadialPolygonWordCycles

/-! DUB-17/18 -> actual cover Abel-Jacobi -> raw reciprocity -> actual polygon word.
The conclusion retains the full cyclic ordering, actual vertex matching,
cotree crossing paths and the closed integer subword cycles needed for the
intersection matrix. The dual-tree and nonempty-complement inputs are
supplied by the constructed original-cover consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
noncomputable section
open SourceCurve Set Real IntegerEdgeChains RadialDissectionTrees CyclicBoundaryWords
open DissectionTrees (nxt nxt_val)
variable {X : Type*} [TopologicalSpace X]

/-- The exact source polygon-word conclusion; existence is proved below. -/
abbrev PolygonWordConclusion (𝒟 : RadialCellDissection X) (𝒯s : Finset 𝒟.ιE) : Prop :=
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let L := {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            ((Cside g true = D ∧ Cside g false = D') ∨
             (Cside g true = D' ∧ Cside g false = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : 𝒟.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : 𝒟.ιV,
          (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f)

theorem exists_polygon_word (𝒟 : RadialCellDissection X)
    (hvert : Function.Injective 𝒟.vert) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s)
    (hL : ∃ e : 𝒟.ιE, e ∉ 𝒯s) : PolygonWordConclusion 𝒟 𝒯s := by
  unfold PolygonWordConclusion
  intro Cside startV endV L m
  classical
  obtain ⟨e₀, he₀⟩ := hL
  have hT : IsTree (fun e => RadialDissectionTrees.Cside 𝒟 e true) (fun e => RadialDissectionTrees.Cside 𝒟 e false) 𝒯s := h𝒯s
  haveI : Nonempty 𝒟.ιC := ⟨RadialDissectionTrees.Cside 𝒟 e₀ true⟩

  have hS₀ := state_init 𝒟 hvert 𝒯s (RadialDissectionTrees.Cside 𝒟 e₀ true)
  obtain ⟨G, ws, hS⟩ := state_final 𝒟 hvert hT (Fintype.card 𝒟.ιC - 1) _ _ _ hS₀ (by
    have : 1 ≤ Fintype.card 𝒟.ιC := Fintype.card_pos
    simp only [Finset.card_singleton]; omega)

  have hG : G = 𝒯s := by
    refine Finset.eq_of_subset_of_card_le hS.hG ?_
    have h1 := spanningTree_card _ _ 𝒯s hT
    have h2 := hS.hcard
    rw [Finset.card_univ] at h2
    omega
  have hmemL : ∀ q : 𝒟.ιE × Bool, q ∈ ws ↔ q.1 ∉ 𝒯s := fun q => by
    rw [hS.hmem, hG]; simp
  have hcyc : Cyc (Corner 𝒟 𝒯s) ws := hG ▸ hS.hcyc

  have hlen : ws.length = m := by
    rw [← List.toFinset_card_of_nodup hS.hnd]
    show ws.toFinset.card = Fintype.card L
    rw [Fintype.card_subtype]
    congr 1
    ext q
    simp [hmemL]
  haveI hm : NeZero m := ⟨(Fintype.card_pos_iff.2 ⟨(⟨(e₀, true), he₀⟩ : L)⟩).ne'⟩
  have hidx : ∀ i : ZMod m, i.val < ws.length := fun i => by rw [hlen]; exact ZMod.val_lt i
  let f : ZMod m → L := fun i => ⟨ws[i.val]'(hidx i), (hmemL _).1 (List.getElem_mem _)⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    simp only [f] at h
    exact ZMod.val_injective m ((hS.hnd.getElem_inj_iff).1 h)
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, by rw [ZMod.card]⟩
  let wd : ZMod m ≃ L := Equiv.ofBijective f hf_bij
  have hwd : ∀ i, (wd i).1 = ws[i.val]'(hidx i) := fun i => rfl

  have hsucc : ∀ i : ZMod m, (i + 1).val = (i.val + 1) % ws.length := fun i => by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, hlen]
  have hcorner : ∀ i : ZMod m, Corner 𝒟 𝒯s (wd i).1 (wd (i + 1)).1 := fun i => by
    rw [hwd, hwd]
    have := cyc_getElem hcyc i.val (hidx i)
    simpa only [hsucc i] using this
  refine ⟨hm, wd, fun i => ⟨(hcorner i).1, ?_⟩, fun e he => ?_⟩
  · obtain ⟨cs, hh, hl, hchain⟩ := exists_list_of_rtg (hcorner i).2
    exact ⟨cs, hh, hl, hchain⟩
  · exact w3_of_w1 𝒟 wd (fun i => (hcorner i).1) e he

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPolygon
