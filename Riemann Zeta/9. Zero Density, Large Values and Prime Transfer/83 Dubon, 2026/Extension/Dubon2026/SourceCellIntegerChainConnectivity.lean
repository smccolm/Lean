import Dubon2026.SourceCellIntegerEdgeBoundary

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

theorem isConn_walk (S : Finset E) (hconn : IsConn hd tl S) : IsWalkConn hd tl S := by
  classical
  intro u v
  by_contra hcontra
  haveI : DecidablePred (Relation.ReflTransGen (adj hd tl S) u ·) :=
    Classical.decPred _
  set A : Finset V := Finset.univ.filter (Relation.ReflTransGen (adj hd tl S) u ·)
  have huA : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ u, .refl⟩
  have hvA : v ∉ A := fun h => hcontra (Finset.mem_filter.mp h).2
  have hedge : ∀ e ∈ S, hd e ∈ A ↔ tl e ∈ A := by
    intro e he
    constructor <;> intro h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e, he, .inl ⟨rfl, rfl⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e, he, .inr ⟨rfl, rfl⟩⟩⟩
  obtain ⟨c, hcS, hcbd⟩ := hconn u v
  have key : ∀ e, (if hd e ∈ A then c e else 0) = (if tl e ∈ A then c e else 0) := by
    intro e
    by_cases heS : e ∈ S
    · by_cases h : hd e ∈ A
      · rw [if_pos h, if_pos ((hedge e heS).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hedge e heS).mpr h'))]
    · rw [hcS e heS]; split_ifs <;> rfl
  have heq : ∀ g : E → V, (∑ w ∈ A, ∑ e with g e = w, c e) =
      ∑ e, (if g e ∈ A then c e else 0) := by
    intro g
    rw [show (∑ w ∈ A, ∑ e with g e = w, c e) =
          ∑ w ∈ A, ∑ e, (if g e = w then c e else 0) from
        Finset.sum_congr rfl (fun w _ => Finset.sum_filter _ _),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_ite_eq A (g e) (fun _ => c e))
  have hsum0 : ∑ w ∈ A, bd hd tl c w = 0 := by
    unfold bd; simp_rw [Finset.sum_sub_distrib, heq hd, heq tl, key, sub_self]
  have hsum1 : ∑ w ∈ A, bd hd tl c w = -1 := by
    simp_rw [hcbd, Finset.sum_sub_distrib, Finset.sum_ite_eq' A v (fun _ => (1:ℤ)),
      Finset.sum_ite_eq' A u (fun _ => (1:ℤ)), if_pos huA, if_neg hvA]
    ring
  exact absurd (hsum0.symm.trans hsum1) (by norm_num)

omit [Fintype V] [DecidableEq E] in

theorem sum_bd_eq (c : E → ℤ) (A : Finset V) :
    ∑ w ∈ A, bd hd tl c w =
      ∑ e, ((if hd e ∈ A then c e else 0) - (if tl e ∈ A then c e else 0)) := by
  classical
  have heq : ∀ g : E → V, (∑ w ∈ A, ∑ e with g e = w, c e) =
      ∑ e, (if g e ∈ A then c e else 0) := by
    intro g
    rw [show (∑ w ∈ A, ∑ e with g e = w, c e) =
          ∑ w ∈ A, ∑ e, (if g e = w then c e else 0) from
        Finset.sum_congr rfl (fun w _ => Finset.sum_filter _ _),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_ite_eq A (g e) (fun _ => c e))
  unfold bd; rw [Finset.sum_sub_distrib, heq hd, heq tl, Finset.sum_sub_distrib]

omit [Fintype V] in

theorem chain_of_walk (S : Finset E) {u v : V}
    (hw : Relation.ReflTransGen (adj hd tl S) u v) :
    ∃ c : E → ℤ, (∀ e ∉ S, c e = 0) ∧
      ∀ w, bd hd tl c w = (if w = v then (1:ℤ) else 0) - (if w = u then 1 else 0) := by
  classical
  induction hw with
  | refl => exact ⟨0, fun _ _ => rfl, fun w => by unfold bd; simp⟩
  | @tail a b _ hab ih =>
    obtain ⟨c₀, hc₀S, hc₀bd⟩ := ih
    obtain ⟨e, heS, heab⟩ := hab
    rcases heab with ⟨hha, htb⟩ | ⟨hhb, hta⟩
    · refine ⟨c₀ + (-1 : ℤ) • (fun e' => if e' = e then (1:ℤ) else 0), ?_, ?_⟩
      · intro e' he'
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc₀S e' he',
          if_neg (fun h : e' = e => he' (h ▸ heS))]; ring
      · intro w
        rw [bd_add, bd_smul, bd_single, hc₀bd w, hha, htb]; split_ifs <;> ring
    · refine ⟨c₀ + (fun e' => if e' = e then (1:ℤ) else 0), ?_, ?_⟩
      · intro e' he'
        simp only [Pi.add_apply, hc₀S e' he',
          if_neg (fun h : e' = e => he' (h ▸ heS))]; ring
      · intro w
        rw [bd_add, bd_single, hc₀bd w, hhb, hta]; split_ifs <;> ring

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
