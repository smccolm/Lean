import Dubon2026.SourceRadialQuotientVertexValues

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The residue-period quotient is an additive group, not a complex vector space.
This exact arc-value algebra is needed to apply the constructed polygon and
integer cycles to logarithmic primitives modulo residues. Reuse the existing
actual radial dissection, polygon endpoints, existing word chains and integer word matrix.
Adapted from S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialArcPeriods
noncomputable section
open Set RadialCellDissection RadialDissectionPeriods
open DissectionPeriods (wordChain wordChain_of_mem)
variable {X : Type*} [TopologicalSpace X]

/-- The integer sign of an oriented edge. -/
def sgn {𝒟 : RadialCellDissection X} (q : 𝒟.ιE × Bool) : ℤ := if q.2 then 1 else -1

theorem ArcValues.B_sub_A {𝒟 : RadialCellDissection X} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) (q : 𝒟.ιE × Bool) :
    B (arcOf 𝒟 q) - A (arcOf 𝒟 q) = sgn q • I q.1 := by
  have := h.hW (arcOf 𝒟 q)
  rw [side_arcOf] at this
  rw [this, sgn]
  split_ifs <;> simp

theorem ArcValues.word_identity {𝒟 : RadialCellDissection X} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, RadialDissectionPolygon.eV 𝒟 (wd i).1 = RadialDissectionPolygon.sV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (RadialDissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ RadialDissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (j : 𝒟.ιE) (hj : j ∉ 𝒯s) :
    J j = -∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val < (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      sgn (wd i).1 • I (wd i).1.1 := by
  classical
  set α : ZMod m := wd.symm ⟨(j, true), hj⟩ with hα
  set β : ZMod m := wd.symm ⟨(j, false), hj⟩ with hβ
  set D : ℕ := (β - α).val with hD
  have hαβ : α ≠ β := by
    intro h'
    have := wd.symm.injective (hα.symm.trans (h'.trans hβ))
    simp at this
  have hD0 : 0 < D := by
    rw [hD, Nat.pos_iff_ne_zero]
    intro h0
    exact hαβ (eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)).symm
  have hwdα : (wd α).1 = (j, true) := by rw [hα, Equiv.apply_symm_apply]
  have hwdβ : (wd β).1 = (j, false) := by rw [hβ, Equiv.apply_symm_apply]
  set T : ZMod m → 𝔸 := fun i => sgn (wd i).1 • I (wd i).1.1 with hT

  have htel : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      A (arcOf 𝒟 (wd (α + d)).1) = B (arcOf 𝒟 (j, true)) + ∑ d' ∈ Finset.Ico 1 d, T (α + d') := by
    intro d hd1 hdD
    induction d with
    | zero => omega
    | succ d ih =>
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · simp only [zero_add, Nat.cast_one, Finset.Ico_self, Finset.sum_empty, add_zero]
        rw [← hwdα]
        exact (h.corner hJ0 (hW1 α).1 (hW1 α).2).symm
      · have ih' := ih hdpos (by omega)
        rw [Finset.sum_Ico_succ_top hdpos, ← add_assoc, ← ih']
        have hc := h.corner hJ0 (hW1 (α + d)).1 (hW1 (α + d)).2
        have hstep := h.B_sub_A (wd (α + d)).1
        push_cast
        rw [← add_assoc, ← hc, hT]
        simp only
        rw [← hstep]
        abel
  have hαD : α + (D : ZMod m) = β := by
    rw [hD, ZMod.natCast_zmod_val]; abel
  have hfinal := htel D hD0 le_rfl
  rw [hαD, hwdβ] at hfinal

  rw [h.hJ1 j, hfinal]
  have hsum : ∑ d' ∈ Finset.Ico 1 D, T (α + d') =
      ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ α ∧ (i - α).val < D), T i := by
    refine Finset.sum_nbij' (fun d' => α + (d' : ZMod m)) (fun i => (i - α).val) ?_ ?_ ?_ ?_ ?_
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by have := ZMod.val_lt (β - α); omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_left,
        ZMod.val_cast_of_lt hd'm]
      refine ⟨fun h' => ?_, hd'.2⟩
      have : ((d' : ℕ) : ZMod m) = 0 := by
        have := congrArg (· - α) h'; simpa using this
      rw [ZMod.natCast_eq_zero_iff] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_Ico]
      refine ⟨Nat.one_le_iff_ne_zero.2 fun h0 => hi.1 ?_, hi.2⟩
      exact eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by have := ZMod.val_lt (β - α); omega
      simp only [add_sub_cancel_left, ZMod.val_cast_of_lt hd'm]
    · intro i hi
      simp only [ZMod.natCast_zmod_val, add_sub_cancel]
    · intro d' hd'
      rfl
  rw [hsum]
  simp only [hT]
  abel


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialArcPeriods
