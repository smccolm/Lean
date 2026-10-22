import Dubon2026.SourceOriginalMeromorphicPathAtlas
import Dubon2026.SourceOriginalRegularLoopJumpClosure

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Endpoint cancellation places each pole-avoiding loop in the actual jump and
residue subgroup. The proved jump containment and native integer-span API give
common integer coefficients for the whole finite family of differentials.
No loop generation hypothesis is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
open scoped Real
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem loop_period_mem_ΛJ [Finite R] {D : CellDissection N}
    (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos D S) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {J : D.ιE → R → ℂ} (hJ : IsJumpH D (hfun S θ Ψ) J)
    {P : Place ℂ F} (δ : Path P P) (hδ : ∀ t, δ t ∉ S) :
    (fun r => pathIntegral N (θ r) δ) ∈ ΛJ D S θ J := by
  choose g hg using fun r => exists_isPrimitiveAlong_of_coeff_mem N (θ r) δ
    (fun t => (δ t).mem_of_ord_nonneg ((hθ r (δ t)).2 (hδ t)))
  have hm := path_sub_mem_G2 S θ hθ hS hP hJ δ hδ g hg
  simp only [sub_self, sub_zero] at hm
  have he : (fun r => pathIntegral N (θ r) δ) = fun r => g r 1 - g r 0 := by
    funext r
    exact pathIntegral_eq_of_isPrimitiveAlong N (hg r)
  rw [he]
  exact hm

/-- Common integer cycle and cell-residue coefficients for a finite family. -/
def MeromorphicFamilyGeneration (D : CellDissection N) (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) : Prop :=
  ∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
    ∃ (a : D.ιE → ℤ) (m : D.ιC → ℤ), ∀ r,
      pathIntegral N (θ r) δ =
        ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N (θ r) (γ l) +
        ∑ C, (m C : ℂ) * (2 * Real.pi * Complex.I * ρ D S θ C r)

theorem meromorphic_family_generation_of_jumps [Finite R] {D : CellDissection N}
    (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos D S) {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {J : D.ιE → R → ℂ} (hJ : IsJumpH D (hfun S θ Ψ) J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hcl : ∀ e, J e ∈ AddSubgroup.closure
      ((fun l r => pathIntegral N (θ r) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ Λres D S θ) :
    MeromorphicFamilyGeneration D S θ T Ts γ := by
  classical
  intro P δ hδ
  have hle : ΛJ D S θ J ≤ AddSubgroup.closure
      ((fun l r => pathIntegral N (θ r) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔ Λres D S θ := by
    refine sup_le ?_ le_sup_right
    rw [AddSubgroup.closure_le]
    rintro _ ⟨e, rfl⟩
    exact hcl e
  have hm := hle (loop_period_mem_ΛJ S θ hθ hS hP hJ δ hδ)
  rw [AddSubgroup.mem_sup] at hm
  obtain ⟨x, hx, y, hy, hxy⟩ := hm
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hx
  obtain ⟨a, ha⟩ := hx
  have hy' : y ∈ Submodule.span ℤ
      (Set.range fun C : D.ιC => (2 * Real.pi * Complex.I) • ρ D S θ C) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy'
  obtain ⟨m, hms⟩ := hy'
  refine ⟨a, m, fun r => ?_⟩
  have he := congrFun hxy r
  rw [← he, ← ha, ← hms]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [zsmul_eq_mul, smul_eq_mul]

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
