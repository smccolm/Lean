import Dubon2026.SourceRadialDissectionGraphConnectivity

/-! DUB-17/18 -> actual cover reciprocity -> 2g remaining geometric edges.
Adapt the proved original dissection argument to the full radial dissection
on the literal cover. Native integer graph chains and spanning-tree results
are reused unchanged. Actual analytic loop realization remains separate.
Source: SourceOriginalCotreeComplementConnectivity and its documented frozen FLT dependency. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
noncomputable section
open SourceCurve Set Real IntegerEdgeChains
open DissectionTrees (nxt nxt_bijective nxt_val nxt_iterate_val)
variable {X : Type*} [TopologicalSpace X] (𝒟 : RadialCellDissection X)

theorem Γconn_sdiff_cotree (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s) :
    IsConn (hdΓ 𝒟) (tlΓ 𝒟) 𝒯sᶜ := by
  classical

  set Cp := fun g => Cside 𝒟 g true
  have hchain : ∀ C : 𝒟.ιC, ∀ g ∈ 𝒯s, ∃! c : 𝒟.ιE → ℤ,
      (∀ e ∉ 𝒯s, c e = 0) ∧ ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) c D =
        (if D = C then (1 : ℤ) else 0) - (if D = Cp g then 1 else 0) :=
    fun C g _ => h𝒯s (Cp g) C

  set ch : 𝒟.ιE → 𝒟.ιC → 𝒟.ιE → ℤ :=
    fun g C => if hg : g ∈ 𝒯s then Classical.choose (hchain C g hg).exists else 0
  have hch_spec : ∀ g ∈ 𝒯s, ∀ C, (∀ e ∉ 𝒯s, ch g C e = 0) ∧
      ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) (ch g C) D =
        (if D = C then (1 : ℤ) else 0) - (if D = Cp g then 1 else 0) := by
    intro g hg C
    simp only [ch, dif_pos hg]
    exact Classical.choose_spec (hchain C g hg).exists
  set Ag : 𝒟.ιE → Finset 𝒟.ιC := fun g => Finset.univ.filter (fun C => ch g C g = 0)

  have hCp_mem : ∀ g ∈ 𝒯s, Cp g ∈ Ag g := by
    intro g hg

    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h0 : (fun _ : 𝒟.ιE => (0 : ℤ)) = ch g (Cp g) :=
      (hchain (Cp g) g hg).unique ⟨fun _ _ => rfl, fun D => by unfold bd; simp⟩
        (hch_spec g hg (Cp g))
    rw [← h0]
  have hCm_notmem : ∀ g ∈ 𝒯s, Cside 𝒟 g false ∉ Ag g := by
    intro g hg hmem

    have hPδg : (∀ e ∉ 𝒯s, (if e = g then (-1:ℤ) else 0) = 0) ∧
        ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
          (fun e => if e = g then (-1:ℤ) else 0) D =
          (if D = Cside 𝒟 g false then (1:ℤ) else 0) - (if D = Cp g then 1 else 0) := by
      refine ⟨fun e he => if_neg (fun (heq : e = g) => he (heq ▸ hg)), fun D => ?_⟩
      have heq : (fun e => if e = g then (-1:ℤ) else 0) =
          (-1 : ℤ) • (fun e => if e = g then (1:ℤ) else 0) :=
        funext (fun e => by simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)
      rw [heq, bd_smul, bd_single]; split_ifs <;> ring
    have hδg : ch g (Cside 𝒟 g false) = (fun e => if e = g then (-1 : ℤ) else 0) :=
      (hchain (Cside 𝒟 g false) g hg).unique (hch_spec g hg _) hPδg
    simp only [Ag, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hδg] at hmem; simp at hmem
  have hAg_edge : ∀ g ∈ 𝒯s, ∀ g' ∈ 𝒯s, g' ≠ g →
      (Cside 𝒟 g' true ∈ Ag g ↔ Cside 𝒟 g' false ∈ Ag g) := by
    intro g hg g' hg' hne

    have hδg' : ∀ e, ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e =
        if e = g' then (1 : ℤ) else 0 := by
      have hP1 : (∀ e ∉ 𝒯s,
            ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e = 0) ∧
          ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
            (fun e => ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e) D =
            (if D = Cside 𝒟 g' true then (1:ℤ) else 0) -
            (if D = Cside 𝒟 g' false then 1 else 0) := by
        refine ⟨fun e he => ?_, fun D => ?_⟩
        · rw [(hch_spec g hg (Cside 𝒟 g' true)).1 e he,
            (hch_spec g hg (Cside 𝒟 g' false)).1 e he]; ring
        · have h1 := (hch_spec g hg (Cside 𝒟 g' true)).2 D
          have h2 := (hch_spec g hg (Cside 𝒟 g' false)).2 D
          rw [show (fun e => ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e) =
                ch g (Cside 𝒟 g' true) - ch g (Cside 𝒟 g' false) from rfl,
            bd_sub, h1, h2]; ring
      have hP2 : (∀ e ∉ 𝒯s, (if e = g' then (1:ℤ) else 0) = 0) ∧
          ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
            (fun e => if e = g' then (1:ℤ) else 0) D =
            (if D = Cside 𝒟 g' true then (1:ℤ) else 0) -
            (if D = Cside 𝒟 g' false then 1 else 0) :=
        ⟨fun e he => if_neg (fun (heq : e = g') => he (heq ▸ hg')),
         fun D => bd_single _ _ g' D⟩
      exact fun e => congrFun
        ((h𝒯s (Cside 𝒟 g' false) (Cside 𝒟 g' true)).unique hP1 hP2) e
    simp only [Ag, Finset.mem_filter, Finset.mem_univ, true_and]
    have hkey := hδg' g
    rw [if_neg (fun h : g = g' => hne h.symm)] at hkey
    omega

  set q : 𝒟.ιE → 𝒟.ιE → ℤ := fun g e => ∑ C ∈ Ag g, cellBdryChain 𝒟 C e
  have hq_cycle : ∀ g ∈ 𝒯s, ∀ w, bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w = 0 := by
    intro g hg w
    have hsum : bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w =
        ∑ C ∈ Ag g, bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w := by
      simp only [q]; rw [bd_finsum]
    rw [hsum, Finset.sum_eq_zero (fun C _ => bd_cellBdryChain 𝒟 hvert C w)]
  have hq_eq : ∀ g e, q g e =
      (if Cside 𝒟 e true ∈ Ag g then (1 : ℤ) else 0) -
      (if Cside 𝒟 e false ∈ Ag g then 1 else 0) := by
    intro g e
    simp only [q]
    simp_rw [cellBdryChain_eq, Finset.sum_sub_distrib,
      Finset.sum_ite_eq (Ag g) (Cside 𝒟 e true) (fun _ => (1:ℤ)),
      Finset.sum_ite_eq (Ag g) (Cside 𝒟 e false) (fun _ => (1:ℤ))]
  have hq_g : ∀ g ∈ 𝒯s, q g g = 1 := by
    intro g hg
    rw [hq_eq, if_pos (hCp_mem g hg), if_neg (hCm_notmem g hg)]; ring
  have hq_g' : ∀ g ∈ 𝒯s, ∀ g' ∈ 𝒯s, g' ≠ g → q g g' = 0 := by
    intro g hg g' hg' hne
    rw [hq_eq]
    rcases (hAg_edge g hg g' hg' hne) with h
    by_cases hm : Cside 𝒟 g' true ∈ Ag g
    · rw [if_pos hm, if_pos (h.mp hm)]; ring
    · rw [if_neg hm, if_neg (fun h' => hm (h.mpr h'))]; ring

  intro u v
  obtain ⟨c, _, hcbd⟩ := Γconn 𝒟 hvert hends u v
  refine ⟨fun e => c e - ∑ g ∈ 𝒯s, c g * q g e, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_compl, not_not] at he
    rw [sub_eq_zero, Finset.sum_eq_single e]
    · rw [hq_g e he, mul_one]
    · intro g hg hne
      rw [hq_g' g hg e he (Ne.symm hne), mul_zero]
    · intro h; exact absurd he h
  · intro w
    have hbd_sub : bd (hdΓ 𝒟) (tlΓ 𝒟) (fun e => c e - ∑ g ∈ 𝒯s, c g * q g e) w =
        bd (hdΓ 𝒟) (tlΓ 𝒟) c w -
        ∑ g ∈ 𝒯s, c g * bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w := by
      have heq : (fun e => c e - ∑ g ∈ 𝒯s, c g * q g e) =
          c - (fun e => ∑ g ∈ 𝒯s, ((c g) • (q g)) e) :=
        funext (fun e => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      rw [heq, bd_sub, bd_finsum]
      congr 1
      exact Finset.sum_congr rfl (fun g _ => bd_smul (hdΓ 𝒟) (tlΓ 𝒟) (c g) (q g) w)
    rw [hbd_sub, hcbd w,
      Finset.sum_eq_zero (fun g hg => by rw [hq_cycle g hg w, mul_zero]), sub_zero]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionTrees
