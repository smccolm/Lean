import Dubon2026.SourceOriginalPrimitiveJumpCirculation

/-! DUB-17/18 -> original Abel-Jacobi -> regular period generation.
The actual vector-valued jumps are circulations. Their proved integer-cycle
decomposition and vanishing on the dual tree reduce their additive subgroup
to the exact 2g complementary edges. This is a jump-generation result; the
path-to-jump and jump-to-period bridges remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
universe u
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}

theorem vector_decomposition_of_scalar_lift (D : CellDissection N)
    {T : Finset D.ιE} {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ f : D.ιE → ULift.{u} ℂ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j) :
    ∀ f : D.ιE → κ → ℂ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  intro f hf e
  funext i
  have he := hZ (fun e => (AddEquiv.ulift : ULift.{u} ℂ ≃+ ℂ).symm (f e i)) (by
    intro w
    rw [← map_sum, ← map_sum]
    congr 1
    simpa only [Finset.sum_apply] using congrFun (hf w) i) e
  have hh := congrArg (AddEquiv.ulift : ULift.{u} ℂ ≃+ ℂ) he
  simpa only [map_sum, map_zsmul, AddEquiv.apply_symm_apply,
    Finset.sum_apply, Pi.smul_apply] using hh

theorem jumps_kirchhoff (D : CellDissection N) (hv : Function.Injective D.vert)
    {Ψ : κ → D.ιC → ℂ → ℂ} {J : D.ιE → κ → ℂ}
    (hJ : ∀ e i,
      let p := D.arcOf (e, true)
      let n := D.arcOf (e, false)
      ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
        Ψ i p.1 ((D.cell p.1).R.loop s) -
          Ψ i n.1 ((D.cell n.1).ζ ((D.cell p.1).bdry s)) = J e i)
    (w : D.ιV) :
    (∑ e with (D.ends e).2 = w, J e) = ∑ e with (D.ends e).1 = w, J e := by
  funext i
  simp only [Finset.sum_apply]
  exact jump_kirchhoff D hv (Ψ i) (fun e => J e i) (fun e => hJ e i) w

theorem closure_jumps_le (D : CellDissection N) (hv : Function.Injective D.vert)
    {T Ts : Finset D.ιE} {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ f : D.ιE → κ → ℂ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j)
    {Ψ : κ → D.ιC → ℂ → ℂ} {J : D.ιE → κ → ℂ}
    (hJ : ∀ e i,
      let p := D.arcOf (e, true)
      let n := D.arcOf (e, false)
      ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
        Ψ i p.1 ((D.cell p.1).R.loop s) -
          Ψ i n.1 ((D.cell n.1).ζ ((D.cell p.1).bdry s)) = J e i)
    (hJ0 : ∀ e ∈ Ts, J e = 0) :
    AddSubgroup.closure (range J) ≤
      AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)) := by
  classical
  rw [AddSubgroup.closure_le]
  rintro _ ⟨f, rfl⟩
  rw [hZ J (jumps_kirchhoff D hv hJ) f]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  by_cases hjs : j ∈ Ts
  · rw [hJ0 j hjs, smul_zero]
    exact zero_mem _
  · have hm : J j ∈ J '' ((T ∪ Ts)ᶜ : Finset D.ιE) := by
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.coe_compl, Finset.coe_union, mem_compl_iff, mem_union,
        Finset.mem_coe, not_or]
      exact ⟨Finset.mem_compl.mp hj, hjs⟩
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hm) _

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
