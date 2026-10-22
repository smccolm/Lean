import Dubon2026.SourceCellIntegerChainConnectivity

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops -> tree/cotree.
Integer chains retain the actual edge labels needed by period sums. The source
minimal connected subset argument avoids translating a multigraph into a simple
graph and back. These foundations will be consumed by the original dissection
tree/cotree theorem; no loop generation is claimed at this intermediate stage.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (hd tl : E → V)

theorem exists_spanningTree (S : Finset E) (hconn : IsConn hd tl S) :
    ∃ T ⊆ S, IsTree hd tl T ∧ IsWalkConn hd tl T := by
  classical

  have hne : {T : Finset E | T ⊆ S ∧ IsWalkConn hd tl T}.Nonempty :=
    ⟨S, le_refl S, isConn_walk hd tl S hconn⟩
  obtain ⟨T, ⟨hTS, hTwalk⟩, hTmin⟩ :=
    Set.Finite.exists_minimalFor id _ (Set.toFinite _) hne
  refine ⟨T, hTS, ?_, hTwalk⟩

  intro u v
  obtain ⟨c, hcT, hcbd⟩ := chain_of_walk hd tl T (hTwalk u v)
  refine ⟨c, ⟨hcT, hcbd⟩, ?_⟩
  rintro c' ⟨hc'T, hc'bd⟩

  funext e
  by_contra hdne

  have heT : e ∈ T := by
    by_contra he; exact hdne (by rw [hc'T e he, hcT e he])
  set d : E → ℤ := fun e' => c' e' - c e'
  have hdT : ∀ e' ∉ T, d e' = 0 := fun e' he' => by
    simp only [d, hc'T e' he', hcT e' he', sub_zero]
  have hdbd : ∀ w, bd hd tl d w = 0 := fun w => by
    rw [show d = c' - c from rfl, bd_sub, hc'bd w, hcbd w, sub_self]
  have hde : d e ≠ 0 := fun h => hdne (by simp only [d] at h; linarith)

  have hTerase : ¬ IsWalkConn hd tl (T.erase e) := by
    intro hwalk'
    have hsub : T.erase e ⊆ S := (Finset.erase_subset e T).trans hTS
    have hmem : T.erase e ∈ {T' | T' ⊆ S ∧ IsWalkConn hd tl T'} := ⟨hsub, hwalk'⟩
    exact absurd (hTmin hmem (Finset.erase_subset e T) heT) (Finset.notMem_erase e T)

  unfold IsWalkConn at hTerase
  simp only [not_forall] at hTerase
  obtain ⟨u₀, v₀, hv₀⟩ := hTerase
  haveI : DecidablePred (Relation.ReflTransGen (adj hd tl (T.erase e)) u₀ ·) :=
    Classical.decPred _
  set A : Finset V := Finset.univ.filter (Relation.ReflTransGen (adj hd tl (T.erase e)) u₀ ·)
  have hedge : ∀ e' ∈ T.erase e, hd e' ∈ A ↔ tl e' ∈ A := by
    intro e' he'
    refine ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e', he', .inl ⟨rfl, rfl⟩⟩⟩,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e', he', .inr ⟨rfl, rfl⟩⟩⟩⟩
  have hAne : ¬ (hd e ∈ A ↔ tl e ∈ A) := by

    intro hiff
    have hallT : ∀ e' ∈ T, hd e' ∈ A ↔ tl e' ∈ A := by
      intro e' he'
      rcases eq_or_ne e' e with rfl | hne'
      · exact hiff
      · exact hedge e' (Finset.mem_erase.mpr ⟨hne', he'⟩)

    apply hv₀
    have hu₀A : u₀ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩

    have hv₀A : v₀ ∈ A := by
      have h := hTwalk u₀ v₀
      clear hv₀
      induction h with
      | refl => exact hu₀A
      | @tail a b _ hab ih =>
        obtain ⟨e', he'T, heab⟩ := hab
        rcases heab with ⟨hha, htb⟩ | ⟨hhb, hta⟩
        · rw [← htb]; exact (hallT e' he'T).mp (hha ▸ ih)
        · rw [← hhb]; exact (hallT e' he'T).mpr (hta ▸ ih)
    exact (Finset.mem_filter.mp hv₀A).2

  have hsum : ∑ w ∈ A, bd hd tl d w =
      (if hd e ∈ A then d e else 0) - (if tl e ∈ A then d e else 0) := by
    rw [sum_bd_eq]
    rw [Finset.sum_eq_single e]
    · intro e' _ hne'
      by_cases he'T : e' ∈ T
      · have h := hedge e' (Finset.mem_erase.mpr ⟨hne', he'T⟩)
        by_cases hh : hd e' ∈ A
        · rw [if_pos hh, if_pos (h.mp hh), sub_self]
        · rw [if_neg hh, if_neg (fun h' => hh (h.mpr h')), sub_self]
      · rw [hdT e' he'T]; split_ifs <;> ring
    · intro h; exact absurd (Finset.mem_univ e) h
  have hsum0 : ∑ w ∈ A, bd hd tl d w = 0 :=
    Finset.sum_eq_zero (fun w _ => hdbd w)
  rw [hsum0] at hsum

  by_cases hhd : hd e ∈ A <;> by_cases htl : tl e ∈ A
  · exact absurd (iff_of_true hhd htl) hAne
  · rw [if_pos hhd, if_neg htl] at hsum; exact hde (by linarith)
  · rw [if_neg hhd, if_pos htl] at hsum; exact hde (by linarith)
  · exact absurd (iff_of_false hhd htl) hAne

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
