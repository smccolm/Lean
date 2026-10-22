import Dubon2026.SourceCellQuotientWordIdentity

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

/-- The actual integer-cycle sum of additive edge integrals. -/
def zvA {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸] (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → 𝔸) (l : 𝒟.ιE) : 𝔸 := ∑ e, Z l e • I e

theorem sum_word_eq_sum_wordChainA {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸] {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j : 𝒟.ιE) (hj : j ∉ 𝒯s) (I : 𝒟.ιE → 𝔸) :
    ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val <
          (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      sgn (wd i).1 • I (wd i).1.1 =
    ∑ f, wordChain wd j hj f • I f := by
  classical
  simp only [wordChain, sgn]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem sum_chain_smulA {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸] {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (p : 𝒟.ιE → ℤ)
    (hp : ∀ w, (∑ e with (𝒟.ends e).2 = w, p e) = ∑ e with (𝒟.ends e).1 = w, p e)
    (I : 𝒟.ιE → 𝔸) :
    ∑ f, p f • I f = ∑ l ∈ 𝒯ᶜ, p l • zvA Z I l := by
  classical
  have hdec : ∀ f, p f = ∑ l ∈ 𝒯ᶜ, Z l f • p l := hZ p hp
  calc ∑ f, p f • I f = ∑ f, ∑ l ∈ 𝒯ᶜ, (Z l f * p l) • I f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [hdec f]
        simp
    _ = ∑ l ∈ 𝒯ᶜ, ∑ f, (Z l f * p l) • I f := Finset.sum_comm
    _ = ∑ l ∈ 𝒯ᶜ, p l • zvA Z I l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [zvA, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [mul_comm]

theorem ArcValues.jump_formula {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, DissectionPolygon.eV 𝒟 (wd i).1 = DissectionPolygon.sV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (DissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ DissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f)
    (j : 𝒟.ιE) (hj : j ∉ 𝒯s) :
    J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, wordMatrix wd j l • zvA Z I l := by
  classical
  rw [h.word_identity hJ0 wd hW1 j hj, sum_word_eq_sum_wordChainA wd j hj,
    sum_chain_smulA hZ _ (hW3 j hj) I]
  congr 1
  rw [Finset.compl_union]
  have h0 : ∀ l ∈ 𝒯ᶜ, l ∉ 𝒯ᶜ ∩ 𝒯sᶜ → wordChain wd j hj l • zvA Z I l = 0 := by
    intro l hl hl'
    have hls : l ∈ 𝒯s := by
      by_contra h'
      exact hl' (Finset.mem_inter.2 ⟨hl, Finset.mem_compl.2 h'⟩)
    rw [wordChain_of_mem wd j hj hls, zero_smul]
  rw [← Finset.sum_subset Finset.inter_subset_left h0]
  exact Finset.sum_congr rfl fun l _ => by rw [wordMatrix_of_not_mem wd hj]

theorem ArcValues.jump_mem_closure {𝒟 : CellDissection N} {𝔸 : Type*} [AddCommGroup 𝔸]
    {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
    {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}
    (h : ArcValues 𝒟 A B I J rot) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZA : FlowDecomp 𝔸 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, DissectionPolygon.eV 𝒟 (wd i).1 = DissectionPolygon.sV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (DissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ DissectionPolygon.eV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) (f : 𝒟.ιE) :
    J f ∈ AddSubgroup.closure ((zvA Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  rw [hZA J h.kirchhoff f]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  by_cases hjs : j ∈ 𝒯s
  · rw [hJ0 j hjs, smul_zero]; exact zero_mem _
  · refine AddSubgroup.zsmul_mem _ ?_ _
    rw [h.jump_formula hJ0 hZ wd hW1 hW3 j hjs]
    refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun l hl => ?_)
    have hmem : zvA Z I l ∈ (zvA Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := ⟨l, hl, rfl⟩
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcPeriods
