import Dubon2026.SourceRadialMeromorphicQuotientArcValues

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Apply the exact polygon and integer cycles in the additive residue quotient.
Lifting the quotient equality proves that every normalized jump belongs to
the sum of complementary cycle periods and literal cell residue periods.
Adapted from the existing original-curve proof, originating in
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
universe u
noncomputable section
open Set RadialArcPeriods
variable {X R : Type*} [TopologicalSpace X]

theorem residue_quotient_decomposition_of_lift (D : RadialCellDissection X)
    (S : Finset X) (residue : X → R → ℂ) {T : Finset D.ιE} {Z : D.ιE → D.ιE → ℤ}
    (hZ : FlowDecomp (ULift.{u} ((R → ℂ) ⧸ Λres D S residue)) D T Z) :
    FlowDecomp ((R → ℂ) ⧸ Λres D S residue) D T Z := by
  intro f hf e
  have he := hZ (fun e => (AddEquiv.ulift : ULift.{u} ((R → ℂ) ⧸ Λres D S residue) ≃+ _).symm
    (f e)) (by intro w; rw [← map_sum, ← map_sum, hf w]) e
  have hh := congrArg (AddEquiv.ulift : ULift.{u} ((R → ℂ) ⧸ Λres D S residue) ≃+ _) he
  simpa only [map_sum, map_zsmul, AddEquiv.apply_symm_apply] using hh

theorem jump_mem_sup {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) (Ψ : R → D.ιC → ℂ → ℂ) (I : D.ιE → R → ℂ)
    {J : D.ιE → R → ℂ}
    (hAV : ArcValues D (Aq S residue Ψ) (Bq S residue Ψ) (Iq S residue I)
      (fun e => QuotientAddGroup.mk' _ (J e)) (fun C => DissectionTrees.nxt (N := (D.cell C).R.N)))
    {T Ts : Finset D.ιE} (hJ0 : ∀ e ∈ Ts, J e = 0)
    {Z : D.ιE → D.ιE → ℤ} (hZ : FlowDecomp ℤ D T Z)
    (hZq : FlowDecomp ((R → ℂ) ⧸ Λres D S residue) D T Z)
    (hW : RadialDissectionPolygon.PolygonWordConclusion D Ts) (f : D.ιE) :
    J f ∈ AddSubgroup.closure ((RadialDissectionPeriods.zv Z I) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔
      Λres D S residue := by
  classical
  have hJ0q : ∀ e ∈ Ts, QuotientAddGroup.mk' (Λres D S residue) (J e) = 0 := by
    intro e he
    rw [hJ0 e he, map_zero]
  obtain ⟨hm, wd, hW1, hW3⟩ := hW
  letI := hm
  have hq := hAV.jump_mem_closure hJ0q hZ hZq wd hW1 hW3 f
  have himg : (RadialArcPeriods.zvA Z (Iq S residue I)) '' ((T ∪ Ts)ᶜ : Finset D.ιE) =
      QuotientAddGroup.mk' (Λres D S residue) ''
        ((RadialDissectionPeriods.zv Z I) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) := by
    rw [Set.image_image]
    exact Set.image_congr fun l _ => zvA_Iq S residue I Z l
  rw [himg, ← AddMonoidHom.map_closure, AddSubgroup.mem_map] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  rw [QuotientAddGroup.mk'_eq_mk'] at hxe
  obtain ⟨z, hz, hxz⟩ := hxe
  rw [← hxz]
  exact add_mem (AddSubgroup.mem_sup_left hx) (AddSubgroup.mem_sup_right hz)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
