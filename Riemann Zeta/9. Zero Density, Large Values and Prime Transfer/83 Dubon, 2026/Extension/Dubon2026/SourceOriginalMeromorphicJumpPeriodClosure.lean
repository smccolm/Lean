import Dubon2026.SourceOriginalMeromorphicQuotientArcValues

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Apply the same constructed polygon and integer cycle decomposition in the
residue quotient. Every logarithmic jump lies in the sum of the complementary
cycle-period subgroup and the actual residue-period subgroup. The lift only
preserves the universe of the already universal circulation theorem.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
universe u
noncomputable section
open SourceCurve Set KaehlerDifferential ArcPeriods
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem residue_quotient_decomposition_of_lift (D : CellDissection N)
    (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ]) {T : Finset D.ιE} {Z : D.ιE → D.ιE → ℤ}
    (hZ : FlowDecomp (ULift.{u} ((R → ℂ) ⧸ Λres D S θ)) D T Z) :
    FlowDecomp ((R → ℂ) ⧸ Λres D S θ) D T Z := by
  intro f hf e
  have he := hZ (fun e => (AddEquiv.ulift : ULift.{u} ((R → ℂ) ⧸ Λres D S θ) ≃+ _).symm
    (f e)) (by intro w; rw [← map_sum, ← map_sum, hf w]) e
  have hh := congrArg (AddEquiv.ulift : ULift.{u} ((R → ℂ) ⧸ Λres D S θ) ≃+ _) he
  simpa only [map_sum, map_zsmul, AddEquiv.apply_symm_apply] using hh

theorem jump_mem_sup {D : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos D S) (hvert : Function.Injective D.vert)
    {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ} (hP : RegPrimData S θ V Ψ)
    {J : D.ιE → R → ℂ} (hJ : IsJumpH D (hfun S θ Ψ) J)
    {T Ts : Finset D.ιE} (hJ0 : ∀ e ∈ Ts, J e = 0)
    {Z : D.ιE → D.ιE → ℤ} (hZ : FlowDecomp ℤ D T Z)
    (hZq : FlowDecomp ((R → ℂ) ⧸ Λres D S θ) D T Z)
    (hW : DissectionPolygon.PolygonWordConclusion D Ts) (f : D.ιE) :
    J f ∈ AddSubgroup.closure ((zvθ θ Z) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ Λres D S θ := by
  classical
  have hAV := arcValuesH S θ hθ hS hvert hP hJ
  have hJ0q : ∀ e ∈ Ts, QuotientAddGroup.mk' (Λres D S θ) (J e) = 0 := by
    intro e he
    rw [hJ0 e he, map_zero]
  obtain ⟨hm, wd, hW1, hW3⟩ := hW
  letI := hm
  have hq := hAV.jump_mem_closure hJ0q hZ hZq wd hW1 hW3 f
  have himg : (ArcPeriods.zvA Z (Iq S θ)) '' ((T ∪ Ts)ᶜ : Finset D.ιE) =
      QuotientAddGroup.mk' (Λres D S θ) '' ((zvθ θ Z) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) := by
    rw [Set.image_image]
    exact Set.image_congr fun l _ => zvA_Iq S θ Z l
  rw [himg, ← AddMonoidHom.map_closure, AddSubgroup.mem_map] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  rw [QuotientAddGroup.mk'_eq_mk'] at hxe
  obtain ⟨z, hz, hxz⟩ := hxe
  rw [← hxz]
  exact add_mem (AddSubgroup.mem_sup_left hx) (AddSubgroup.mem_sup_right hz)

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
