import Dubon2026.SourceCellQuotientArcValues

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The residue-period quotient is an additive group, not a complex vector space.
This exact arc-value algebra is needed to apply the constructed polygon and
integer cycles to logarithmic primitives modulo residues. Reuse the existing
original dissection, polygon endpoints, word chains and integer word matrix.
Adapted from S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
noncomputable section
open Set CellDissection DissectionPeriods
variable {N : ℕ} [NeZero N]

open scoped Classical in

/-- The value at a cell vertex, selected by its injective starting arcs. -/
noncomputable def vval (𝒟 : CellDissection N) {𝔸 : Type*} [AddCommGroup 𝔸] (A : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸)
    (C : 𝒟.ιC) (v : 𝒟.ιV) : 𝔸 :=
  ∑ k : Fin (𝒟.cell C).R.N, if sv 𝒟 ⟨C, k⟩ = v then A ⟨C, k⟩ else 0

theorem ArcValues.vval_sv {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) :
    vval 𝒟 A C (sv 𝒟 ⟨C, k⟩) = A ⟨C, k⟩ := by
  classical
  unfold vval
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hne
    rw [if_neg]
    exact fun heq => hne (h.hinj C heq)
  · simp

theorem ArcValues.B_eq_vval {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    B p = vval 𝒟 A p.1 (ev 𝒟 p) := by
  obtain ⟨C, k⟩ := p
  rw [h.hrot C k, h.vval_sv, h.hC]

theorem ArcValues.A_eq_vval {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    A p = vval 𝒟 A p.1 (sv 𝒟 p) := by
  obtain ⟨C, k⟩ := p
  rw [h.vval_sv]

theorem ArcValues.vval_eq_of_link {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) {g : 𝒟.ιE} (hg : J g = 0)
    {v : 𝒟.ιV} (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) {D D' : 𝒟.ιC}
    (hDD' : ((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
      ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) :
    vval 𝒟 A D v = vval 𝒟 A D' v := by
  have hkey : vval 𝒟 A (arcOf 𝒟 (g, true)).1 v = vval 𝒟 A (arcOf 𝒟 (g, false)).1 v := by
    rcases hv with rfl | rfl
    ·
      have h1 : A (arcOf 𝒟 (g, true)) = vval 𝒟 A (arcOf 𝒟 (g, true)).1 (𝒟.ends g).1 := by
        rw [h.A_eq_vval, sv_arcOf]; rfl
      have h2 : B (arcOf 𝒟 (g, false)) = vval 𝒟 A (arcOf 𝒟 (g, false)).1 (𝒟.ends g).1 := by
        rw [h.B_eq_vval, ev_arcOf]; rfl
      rw [← h1, ← h2]
      exact sub_eq_zero.1 ((h.hJ2 g).symm.trans hg)
    ·
      have h1 : B (arcOf 𝒟 (g, true)) = vval 𝒟 A (arcOf 𝒟 (g, true)).1 (𝒟.ends g).2 := by
        rw [h.B_eq_vval, ev_arcOf]; rfl
      have h2 : A (arcOf 𝒟 (g, false)) = vval 𝒟 A (arcOf 𝒟 (g, false)).1 (𝒟.ends g).2 := by
        rw [h.A_eq_vval, sv_arcOf]; rfl
      rw [← h1, ← h2]
      exact sub_eq_zero.1 ((h.hJ1 g).symm.trans hg)
  rcases hDD' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hkey
  · exact hkey.symm

theorem ArcValues.corner {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {q q' : 𝒟.ιE × Bool} (hv : DissectionPolygon.eV 𝒟 q = DissectionPolygon.sV 𝒟 q')
    (hcs : ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 q).1 ∧
      cs.getLast? = some (arcOf 𝒟 q').1 ∧
      cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
        (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
          ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
        (DissectionPolygon.eV 𝒟 q = (𝒟.ends g).1 ∨ DissectionPolygon.eV 𝒟 q = (𝒟.ends g).2))) :
    B (arcOf 𝒟 q) = A (arcOf 𝒟 q') := by
  obtain ⟨cs, hhd, hlast, hch⟩ := hcs
  rw [h.B_eq_vval, h.A_eq_vval, ev_arcOf, sv_arcOf, ← hv]
  set v := DissectionPolygon.eV 𝒟 q with hvdef
  have hall : ∀ D ∈ cs, vval 𝒟 A D v = vval 𝒟 A (arcOf 𝒟 q).1 v := by
    refine hch.induction (fun D => vval 𝒟 A D v = vval 𝒟 A (arcOf 𝒟 q).1 v) cs ?_ ?_
    · rintro D D' ⟨g, hg, hDD', hvg⟩ hD
      rw [← hD]
      exact (h.vval_eq_of_link (hJ0 g hg) hvg hDD').symm
    · intro hne
      obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.1 hhd
      rfl
  exact (hall _ (List.mem_of_getLast? hlast)).symm


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
