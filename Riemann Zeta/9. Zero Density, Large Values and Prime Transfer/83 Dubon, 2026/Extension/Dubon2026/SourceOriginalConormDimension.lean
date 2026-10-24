import Dubon2026.SourceOriginalConormDivisorSpaces
import Dubon2026.SourceOriginalComplexFieldIndependence
import Dubon2026.SourceOriginalGenusBound

/-! DUB-17/18 -> modular good reduction -> arithmetic numerical genus.
The existing coefficient independence and the proved divisor-space span
give a basis of the actual complex conorm space. Thus its dimension equals
the arithmetic divisor-space dimension, with no basis or descent premise. -/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem ell_conorm (D : Divisor Qbar FQ) : ell (conorm N D) = ell D := by
  classical
  haveI := finite_original_lSpace N Qbar D
  let b := Module.finBasis Qbar (LSpace D)
  let e (i : Fin (ell D)) : LSpace (conorm N D) :=
    ⟨fieldMap N (b i).val, fieldMap_mem_lSpace_conorm N D (b i).property⟩
  have hli : LinearIndependent ℂ e := by
    have h := fieldMap_linearIndependent N
      (b.linearIndependent.map' (LSpace D).subtype (Submodule.ker_subtype _))
    exact h.of_comp (LSpace (conorm N D)).subtype
  have hspan : Submodule.span ℂ (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ _hz
    have hmem := lSpace_conorm_subset_span N D hz
    have himage : Submodule.span ℂ ((fieldMap N) '' (LSpace D : Set FQ)) =
        Submodule.span ℂ (Set.range fun i => fieldMap N (b i).val) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, rfl⟩
        have hg' : fieldMap N g = ∑ i, sigma (b.repr ⟨g, hg⟩ i) •
            fieldMap N (b i).val := by
          conv_lhs => rw [show g = (⟨g, hg⟩ : LSpace D).val from rfl,
            ← b.sum_repr ⟨g, hg⟩]
          simp only [Submodule.coe_sum, SetLike.val_smul, map_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Algebra.smul_def, map_mul, fieldMap_constants, Algebra.smul_def]
        rw [hg']
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, (b i).property, rfl⟩)
    rw [himage] at hmem
    have hmap : Submodule.span ℂ (Set.range fun i => fieldMap N (b i).val) =
        (Submodule.span ℂ (Set.range e)).map (LSpace (conorm N D)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hmem
    obtain ⟨y, hy, hyz⟩ := hmem
    rwa [show y = ⟨z, hz⟩ from Subtype.ext hyz] at hy
  let b' : Module.Basis (Fin (ell D)) ℂ (LSpace (conorm N D)) :=
    Module.Basis.mk hli hspan.symm.le
  exact (Module.finrank_eq_card_basis b').trans (Fintype.card_fin _)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
