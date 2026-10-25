import Dubon2026.SourceRadialMeromorphicPrimitiveValues
import Dubon2026.SourceRadialCellJumpDifferences

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Compare principal-log cell readings modulo actual residue periods, then use
the constructed paired-arc jumps and original carrier intersection chains.
The exact readings will anchor the global pole-avoiding path atlas.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Filter Complex RadialCellDissection RadialDissectionPeriods
open scoped Real Topology
variable {X R : Type*} [TopologicalSpace X]

theorem pval_sub_mem_of_linkedAt {𝒟 : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) {Ψ : R → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → R → ℂ}
    (hJ : IsJumpH 𝒟 (hfun S residue Ψ) J) {x : X} {D E : 𝒟.ιC} (h : LinkedAt 𝒟 x D E) :
    pval S residue Ψ D x - pval S residue Ψ E x ∈ ΛJ 𝒟 S residue J := by
  obtain ⟨k, k', he, hx⟩ := h
  set e := (𝒟.side D k).1 with hedef
  by_cases hs : (𝒟.side D k).2 = (𝒟.side E k').2
  · have heq : 𝒟.side D k = 𝒟.side E k' := Prod.ext he hs
    have := 𝒟.side_bij.injective (a₁ := ⟨D, k⟩) (a₂ := ⟨E, k'⟩) heq
    cases this
    rw [sub_self]
    exact zero_mem _
  have hDk : ∀ (σ : Bool), (𝒟.side D k).2 = σ → arcOf 𝒟 (e, σ) = ⟨D, k⟩ := by
    intro σ hσ
    have : 𝒟.side D k = (e, σ) := Prod.ext rfl hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨D, k⟩
  have hEk : ∀ (σ : Bool), (𝒟.side E k').2 = σ → arcOf 𝒟 (e, σ) = ⟨E, k'⟩ := by
    intro σ hσ
    have : 𝒟.side E k' = (e, σ) := Prod.ext he.symm hσ
    rw [← this]; exact arcOf_side 𝒟 ⟨E, k'⟩

  have hjump : ∃ y ∈ Λres 𝒟 S residue,
      pval S residue Ψ (arcOf 𝒟 (e, true)).1 x - pval S residue Ψ (arcOf 𝒟 (e, false)).1 x = J e + y := by
    obtain ⟨ψ, -, -, -, hbd, hJe⟩ := hJ e

    have hx' : x ∈ (𝒟.cell (arcOf 𝒟 (e, false)).1).arc (arcOf 𝒟 (e, false)).2 := by
      have hside : (𝒟.side D k).1 = (𝒟.side (arcOf 𝒟 (e, false)).1 (arcOf 𝒟 (e, false)).2).1 := by
        rw [side_arcOf]
      rwa [arc_eq_of_side 𝒟 D k _ _ hside] at hx
    obtain ⟨z, ⟨t, ht, rfl⟩, rfl⟩ := hx'
    have hxm : (𝒟.cell (arcOf 𝒟 (e, false)).1).ζ.symm ((𝒟.cell (arcOf 𝒟 (e, false)).1).R.loop t) =
        (𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t := rfl
    rw [hxm]
    have h1 := hfun_sub_pval_mem S residue Ψ (arcOf 𝒟 (e, true)).1 (ψ t)
    have h2 := hfun_sub_pval_mem S residue Ψ (arcOf 𝒟 (e, false)).1 t
    rw [← hbd t ht] at h1
    refine ⟨(hfun S residue Ψ (arcOf 𝒟 (e, false)).1 t -
      pval S residue Ψ (arcOf 𝒟 (e, false)).1 ((𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t)) -
      (hfun S residue Ψ (arcOf 𝒟 (e, true)).1 (ψ t) -
        pval S residue Ψ (arcOf 𝒟 (e, true)).1 ((𝒟.cell (arcOf 𝒟 (e, false)).1).bdry t)),
      sub_mem h2 h1, ?_⟩
    rw [← hJe t ht]
    abel
  have hΛ : ∀ {z : R → ℂ}, (∃ y ∈ Λres 𝒟 S residue, z = J e + y) → z ∈ ΛJ 𝒟 S residue J := by
    rintro _ ⟨b, hb, rfl⟩
    have hmem : J e ∈ Set.range J := ⟨e, rfl⟩
    exact add_mem (AddSubgroup.mem_sup_left (AddSubgroup.subset_closure hmem))
      (AddSubgroup.mem_sup_right hb)
  cases hD2 : (𝒟.side D k).2
  · have hE2 : (𝒟.side E k').2 = true := by
      cases h' : (𝒟.side E k').2
      · exact absurd (hD2.trans h'.symm) hs
      · rfl
    rw [hDk false hD2, hEk true hE2] at hjump
    have := hΛ hjump
    rw [← neg_sub]
    exact neg_mem this
  · have hE2 : (𝒟.side E k').2 = false := by
      cases h' : (𝒟.side E k').2
      · rfl
      · exact absurd (hD2.trans h'.symm) hs
    rw [hDk true hD2, hEk false hE2] at hjump
    exact hΛ hjump


theorem pval_sub_mem {𝒟 : RadialCellDissection X} (S : Finset (X))
    (residue : X → R → ℂ) {Ψ : R → 𝒟.ιC → ℂ → ℂ} {J : 𝒟.ιE → R → ℂ}
    (hJ : IsJumpH 𝒟 (hfun S residue Ψ) J) {x : X} {D E : 𝒟.ιC}
    (hD : x ∈ (𝒟.cell D).carrier) (hE : x ∈ (𝒟.cell E).carrier) :
    pval S residue Ψ D x - pval S residue Ψ E x ∈ ΛJ 𝒟 S residue J := by
  have hchain := 𝒟.inter D E x hD hE
  clear hD hE
  induction hchain with
  | refl => rw [sub_self]; exact zero_mem _
  | tail _ hBC ih =>
    have := add_mem ih (pval_sub_mem_of_linkedAt S residue hJ hBC)
    rwa [sub_add_sub_cancel] at this

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
