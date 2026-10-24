import Dubon2026.SourceOriginalPrincipalDescent
import Dubon2026.SourceOriginalComplexSpanDescent
import Dubon2026.SourceOriginalRegularFinite

/-! DUB-17/18 -> modular good reduction -> genus equality. The original
arithmetic-to-complex conorm preserves divisor-space membership. Conversely,
the existing function-span descent and independent-coefficient order bound
express every complex section in the span of arithmetic sections. This is
the exact dimension-comparison input for the arithmetic numerical genus;
no general theory of arbitrary constant extensions is introduced. -/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem fieldMap_mem_lSpace_conorm (D : Divisor Qbar FQ) {f : FQ}
    (hf : f ∈ LSpace D) : fieldMap N f ∈ LSpace (conorm N D) := by
  classical
  rcases mem_lSpace_iff_ord.mp hf with rfl | hf
  · rw [map_zero]
    exact zero_mem _
  apply mem_lSpace_iff_ord.mpr
  right
  intro w
  by_cases hw : ∃ v, w = liftPlace N v
  · obtain ⟨v, rfl⟩ := hw
    rw [conorm_apply_liftPlace, ord_liftPlace]
    exact hf v
  · push Not at hw
    rw [conorm_apply_of_forall_ne N D hw, ord_phi_of_forall_ne N hw, neg_zero]

theorem lSpace_conorm_subset_span (D : Divisor Qbar FQ) {z : FC}
    (hz : z ∈ LSpace (conorm N D)) :
    z ∈ Submodule.span ℂ ((fieldMap N) '' (LSpace D : Set FQ)) := by
  classical
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  have hzord := (mem_lSpace_iff_ord.mp hz).resolve_left hz0
  have hzspan := original_mem_span_of_regular_off_image N z (by
    intro W hW
    apply W.mem_of_ord_nonneg
    simpa only [conorm_apply_of_forall_ne N D hW, neg_zero] using hzord W)
  obtain ⟨n, β, u, hβ, hzu⟩ := ConstantField.exists_linearIndependent_repr
    (K := Qbar) (F := FQ) (K' := ℂ) (F' := FC) hzspan
  have hu (i : Fin n) : u i ∈ LSpace D := by
    apply mem_lSpace_iff_ord.mpr
    rcases eq_or_ne (u i) 0 with hi | hi
    · exact Or.inl hi
    right
    intro P
    have h := ConstantField.ord_sum_le P (liftPlace N P)
      (original_place_residue_algebraMap_bijective N Qbar P).surjective
      (liftPlace_comap N P) (ord_liftPlace N P) Finset.univ β hβ u
      (Finset.mem_univ i) hi
    rw [← hzu] at h
    have hP := hzord (liftPlace N P)
    rw [conorm_apply_liftPlace] at hP
    exact hP.trans h
  rw [hzu]
  apply Submodule.sum_mem
  intro i _hi
  change β i • fieldMap N (u i) ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u i, hu i, rfl⟩)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
