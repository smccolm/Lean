import Dubon2026.SourceRadialDissectionBoundaryChains

/-! DUB-17/18 -> actual cover reciprocity -> 2g remaining geometric edges.
Adapt the proved original dissection argument to the full radial dissection
on the literal cover. Native integer graph chains and spanning-tree results
are reused unchanged. Actual analytic loop realization remains separate.
Source: SourceOriginalDissectionGraphConnectivity and its documented frozen FLT dependency. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
noncomputable section
open SourceCurve Set Real IntegerEdgeChains
open DissectionTrees (nxt nxt_bijective nxt_val nxt_iterate_val)
variable {X : Type*} [TopologicalSpace X] (𝒟 : RadialCellDissection X)

theorem Γconn (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v) :
    IsConn (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ := by
  classical

  set sV : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → 𝒟.ιV := fun C k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1 else (𝒟.ends (𝒟.side C k).1).2

  have hintra : ∀ (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N),
      adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ (sV C k) (sV C (nxt k)) := by
    intro C k
    refine ⟨(𝒟.side C k).1, Finset.mem_univ _, ?_⟩

    have heV : sV C (nxt k) =
        if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).2
        else (𝒟.ends (𝒟.side C k).1).1 := by
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
      simp only [sV]
      rw [← h1, ← h2, hb]
    have hsVk : sV C k = if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1
        else (𝒟.ends (𝒟.side C k).1).2 := rfl
    simp only [hdΓ, tlΓ]
    by_cases hσ : (𝒟.side C k).2
    · rw [show sV C k = (𝒟.ends (𝒟.side C k).1).1 from hsVk.trans (if_pos hσ),
        show sV C (nxt k) = (𝒟.ends (𝒟.side C k).1).2 from heV.trans (if_pos hσ)]
      exact .inr ⟨rfl, rfl⟩
    · rw [show sV C k = (𝒟.ends (𝒟.side C k).1).2 from hsVk.trans (if_neg hσ),
        show sV C (nxt k) = (𝒟.ends (𝒟.side C k).1).1 from heV.trans (if_neg hσ)]
      exact .inl ⟨rfl, rfl⟩

  have hcell : ∀ (C : 𝒟.ιC) (k k' : Fin (𝒟.cell C).R.N),
      Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k) (sV C k') := by
    intro C k k'
    suffices h : ∀ m, Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ)
        (sV C k) (sV C (nxt^[m] k)) by
      have heq : nxt^[k'.val + (𝒟.cell C).R.N - k.val] k = k' := by
        apply Fin.ext
        rw [nxt_iterate_val]
        have hk := k.isLt; have hk' := k'.isLt
        rw [show k.val + (k'.val + (𝒟.cell C).R.N - k.val) = k'.val + (𝒟.cell C).R.N
          from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
      exact heq ▸ h (k'.val + (𝒟.cell C).R.N - k.val)
    intro m
    induction m with
    | zero => exact .refl
    | succ n ih =>
      rw [Function.iterate_succ']
      exact ih.tail (hintra C (nxt^[n] k))

  have hcross : ∀ C C' : 𝒟.ιC, ∀ (k₀ : Fin (𝒟.cell C).R.N) (k₀' : Fin (𝒟.cell C').R.N),
      Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k₀) (sV C' k₀') := by
    intro C C' k₀ k₀'
    suffices h : ∀ C C', Relation.ReflTransGen
        (fun A B : 𝒟.ιC => ∃ (k : Fin (𝒟.cell A).R.N) (k' : Fin (𝒟.cell B).R.N),
          (𝒟.side A k).1 = (𝒟.side B k').1) C C' →
        ∀ (k₀ : Fin (𝒟.cell C).R.N), ∃ (k' : Fin (𝒟.cell C').R.N),
          Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k₀) (sV C' k') by
      obtain ⟨k', hk'⟩ := h C C' (𝒟.conn C C') k₀
      exact hk'.trans (hcell C' k' k₀')
    intro C C' hconn
    induction hconn with
    | refl => exact fun k₀ => ⟨k₀, .refl⟩
    | @tail B B' _ hBB' ih =>
      intro k₀
      obtain ⟨kB, hkB⟩ := ih k₀
      obtain ⟨k, k', hedge⟩ := hBB'
      by_cases hsame : (𝒟.side B k).2 = (𝒟.side B' k').2
      ·
        have hinj : (⟨B, k⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨B', k'⟩ :=
          𝒟.side_bij.injective (a₁ := ⟨B, k⟩) (a₂ := ⟨B', k'⟩) (Prod.ext hedge hsame)
        obtain rfl : B = B' := congrArg Sigma.fst hinj
        exact ⟨k', hkB.trans (hcell B kB k')⟩
      ·
        refine ⟨k', (hkB.trans (hcell B kB k)).tail ?_⟩
        refine ⟨(𝒟.side B k).1, Finset.mem_univ _, ?_⟩
        have hopp : (𝒟.side B' k').2 = !(𝒟.side B k).2 := by
          revert hsame
          rcases (𝒟.side B k).2 <;> rcases (𝒟.side B' k').2 <;> simp
        simp only [sV, hdΓ, tlΓ, ← hedge, hopp]
        by_cases hσ : (𝒟.side B k).2 <;>
          simp only [hσ, Bool.not_true, Bool.not_false, if_true, if_false,
            Bool.false_eq_true]
        · exact .inr ⟨trivial, trivial⟩
        · exact .inl ⟨trivial, trivial⟩

  have hevery : ∀ v : 𝒟.ιV, ∃ (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N), sV C k = v := by
    intro v
    obtain ⟨e, he⟩ := hends v

    rcases he with htl | hhd
    ·
      set p := Function.surjInv 𝒟.side_bij.surjective (e, true)
      have hp := Function.surjInv_eq 𝒟.side_bij.surjective (e, true)
      refine ⟨p.1, p.2, ?_⟩
      simp only [sV, show (𝒟.side p.1 p.2) = (e, true) from hp]
      exact htl
    · set p := Function.surjInv 𝒟.side_bij.surjective (e, false)
      have hp := Function.surjInv_eq 𝒟.side_bij.surjective (e, false)
      refine ⟨p.1, p.2, ?_⟩
      simp only [sV, show (𝒟.side p.1 p.2) = (e, false) from hp,
        if_neg (by simp : ¬ (false = true))]
      exact hhd

  intro u v
  obtain ⟨Cu, ku, hu⟩ := hevery u
  obtain ⟨Cv, kv, hv⟩ := hevery v
  exact chain_of_walk _ _ _ (hu ▸ hv ▸ hcross Cu Cv ku kv)

theorem Γstar_conn : IsConn (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
    Finset.univ := by
  classical
  intro C C'
  induction 𝒟.conn C C' with
  | refl => exact ⟨0, fun e he => absurd (Finset.mem_univ e) he, fun w => by unfold bd; simp⟩
  | @tail A B _ hstep ih =>
    obtain ⟨c₀, _, hc₀⟩ := ih
    obtain ⟨k, k', hkk'⟩ := hstep
    set e := (𝒟.side A k).1 with he_def
    have hA : Cside 𝒟 e (𝒟.side A k).2 = A :=
      (Cside_eq_iff 𝒟 e (𝒟.side A k).2 A).mpr ⟨k, Prod.ext he_def.symm rfl⟩
    have hB : Cside 𝒟 e (𝒟.side B k').2 = B :=
      (Cside_eq_iff 𝒟 e (𝒟.side B k').2 B).mpr ⟨k', Prod.ext (he_def ▸ hkk'.symm) rfl⟩
    by_cases hAB : A = B
    · subst hAB; exact ⟨c₀, fun e' he' => absurd (Finset.mem_univ e') he', hc₀⟩
    have hσ : (𝒟.side A k).2 ≠ (𝒟.side B k').2 := by
      intro hσeq
      have : (⟨A, k⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨B, k'⟩ :=
        𝒟.side_bij.injective (Prod.ext (he_def ▸ hkk') hσeq)
      exact hAB (congrArg Sigma.fst this)
    set sgn : ℤ := if (𝒟.side A k).2 then -1 else 1
    refine ⟨c₀ + sgn • (fun e' => if e' = e then (1:ℤ) else 0),
      fun e' he' => absurd (Finset.mem_univ e') he', fun D => ?_⟩
    rw [bd_add, bd_smul, hc₀ D, bd_single]
    cases hσA : (𝒟.side A k).2 with
    | false =>
      have hσB : (𝒟.side B k').2 = true := by
        cases h : (𝒟.side B k').2
        · exact absurd (hσA.trans h.symm) hσ
        · rfl
      rw [show Cside 𝒟 e true = B from hσB ▸ hB,
          show Cside 𝒟 e false = A from hσA ▸ hA]
      simp only [sgn, hσA, reduceCtorEq, if_false, one_mul]
      split_ifs <;> ring
    | true =>
      have hσB : (𝒟.side B k').2 = false := by
        cases h : (𝒟.side B k').2
        · rfl
        · exact absurd (hσA.trans h.symm) hσ
      rw [show Cside 𝒟 e true = A from hσA ▸ hA,
          show Cside 𝒟 e false = B from hσB ▸ hB]
      simp only [sgn, hσA, if_true, neg_one_mul, neg_sub]
      split_ifs <;> ring

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
