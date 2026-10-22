import Dubon2026.SourceOriginalArithmeticFieldAction
import Mathlib.FieldTheory.Galois.Infinite

/-! DUB-17/18 -> modular Galois association -> continuous action on
original divisor-class torsion -> finite fields of definition of original
functions and places. Every element of the actual rationally generated
Laurent field uses only finitely many algebraic coefficients. Native finite
simple extensions and their composita therefore supply a finite field
whose fixing subgroup fixes that same original function.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_JZero_isOpen_stabilizer, FiniteLevel only.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ

private theorem original_laurent_fieldOfDefinition (N : ℕ) {x : LaurentSeries Qbar}
    (hx : x ∈ modularFunctionFieldOver N Qbar) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → coeffMap (σ : Qbar →+* Qbar) x = x := by
  letI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Qbar := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  change x ∈ Subfield.closure (Set.range (algebraMap Qbar (LaurentSeries Qbar)) ∪
    (coeffEmb Qbar '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ)))) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, _, rfl⟩
    · refine ⟨IntermediateField.adjoin ℚ {a},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) a), fun σ hσ => ?_⟩
      have ha : σ a = a := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ a
        (IntermediateField.mem_adjoin_simple_self ℚ a)
      rw [coeffMap_original_constants, ha]
    · exact ⟨⊥, inferInstance, fun σ _ => coeffMap_coeffEmb σ z⟩
  | one => exact ⟨⊥, inferInstance, fun _ _ => map_one _⟩
  | add x y _ _ hx hy =>
    obtain ⟨Ex, hEx, hfixx⟩ := hx
    obtain ⟨Ey, hEy, hfixy⟩ := hy
    letI := hEx
    letI := hEy
    refine ⟨Ex ⊔ Ey, inferInstance, fun σ hσ => ?_⟩
    rw [map_add, hfixx σ (IntermediateField.fixingSubgroup_le le_sup_left hσ),
      hfixy σ (IntermediateField.fixingSubgroup_le le_sup_right hσ)]
  | neg x _ hx =>
    obtain ⟨E, hE, hfix⟩ := hx
    exact ⟨E, hE, fun σ hσ => by rw [map_neg, hfix σ hσ]⟩
  | inv x _ hx =>
    obtain ⟨E, hE, hfix⟩ := hx
    exact ⟨E, hE, fun σ hσ => by rw [map_inv₀, hfix σ hσ]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Ex, hEx, hfixx⟩ := hx
    obtain ⟨Ey, hEy, hfixy⟩ := hy
    letI := hEx
    letI := hEy
    refine ⟨Ex ⊔ Ey, inferInstance, fun σ hσ => ?_⟩
    rw [map_mul, hfixx σ (IntermediateField.fixingSubgroup_le le_sup_left hσ),
      hfixy σ (IntermediateField.fixingSubgroup_le le_sup_right hσ)]

theorem original_function_fieldOfDefinition (N : ℕ) (x : modularFunctionFieldOver N Qbar) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → originalArithmeticRingAut N σ x = x := by
  obtain ⟨E, hE, hfix⟩ := original_laurent_fieldOfDefinition N x.property
  exact ⟨E, hE, fun σ hσ => Subtype.ext (hfix σ hσ)⟩

end
end Dubon2026.SourceFunctionField
