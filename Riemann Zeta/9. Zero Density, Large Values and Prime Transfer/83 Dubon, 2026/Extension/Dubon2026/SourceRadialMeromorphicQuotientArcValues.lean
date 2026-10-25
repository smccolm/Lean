import Dubon2026.SourceRadialQuotientArcGeometry
import Dubon2026.SourceRadialMeromorphicSignedEndpoints

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Exact paired jumps give signed endpoint increments, while one full boundary
turn changes the reading by a residue period. Thus the actual logarithmic
readings satisfy every additive polygon clause in the residue quotient.
Adapted from the existing original-curve proof, originating in
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Complex RadialArcPeriods RadialCellDissection
open DissectionTrees (nxt nxt_bijective)
open ArcPeriods (castSucc_nxt_of_lt castSucc_nxt_of_not_lt)
open scoped Real
variable {X R : Type*} [TopologicalSpace X]

theorem arcValuesH {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) (Ψ : R → D.ιC → ℂ → ℂ)
    (hvert : Function.Injective D.vert) {J : D.ιE → R → ℂ}
    (hJ : IsJumpH D (hfun S residue Ψ) J) (I : D.ιE → R → ℂ)
    (hpos : ∀ e, hfun S residue Ψ (D.arcOf (e, true)).1
        ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ) -
      hfun S residue Ψ (D.arcOf (e, true)).1
        ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc) = I e) :
    ArcValues D (Aq S residue Ψ) (Bq S residue Ψ) (Iq S residue I)
      (fun e => QuotientAddGroup.mk' _ (J e)) (fun C => nxt (N := (D.cell C).R.N)) := by
  refine ⟨?_, fun _ => nxt_bijective, ?_, ?_, ?_, ?_, fun C => sv_injective D C⟩
  · rintro ⟨C, k⟩
    have h := hJ.signed_endpoint_increment I hpos (D.side C k)
    rw [D.arcOf_side ⟨C, k⟩] at h
    simp only [Aq, Bq, Iq, ← map_sub, h]
    split_ifs <;> simp only [map_neg]
  · exact fun C k => RadialDissectionPolygon.corner_arc D hvert C k
  ·
    intro C k
    simp only [Aq, Bq]
    by_cases hk : k.val + 1 < (D.cell C).R.N
    · rw [castSucc_nxt_of_lt k hk]
    · obtain ⟨h0, hl⟩ := castSucc_nxt_of_not_lt k hk
      rw [h0, hl, (D.cell C).R.hφ0, (D.cell C).R.hφN, QuotientAddGroup.mk'_eq_mk']
      refine ⟨(2 * π * Complex.I) • ρ D S residue C, AddSubgroup.subset_closure ⟨C, rfl⟩, ?_⟩
      rw [← hfun_add_two_pi, zero_add]
  ·
    intro e
    obtain ⟨ψ, -, ha, -, -, hJe⟩ := hJ e
    have := hJe _ (left_mem_Icc.2 ((D.cell (arcOf D (e, false)).1).R.hmono Fin.castSucc_lt_succ).le)
    rw [ha] at this
    simp only [Aq, Bq, ← map_sub, this]
  ·
    intro e
    obtain ⟨ψ, -, -, hb, -, hJe⟩ := hJ e
    have := hJe _ (right_mem_Icc.2 ((D.cell (arcOf D (e, false)).1).R.hmono Fin.castSucc_lt_succ).le)
    rw [hb] at this
    simp only [Aq, Bq, ← map_sub, this]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
