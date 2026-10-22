import Dubon2026.SourceOriginalPairBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> actual constant-field extension. The map acts on the literal original Laurent
coefficients and preserves both original j generators. Existing coefficient
composition and original pair generation avoid a new function-field model.
Adapted from S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, coefficient-map section only.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ

/-- A fixed rational embedding of the original algebraic closure into the complex numbers. -/
def sigma : Qbar →ₐ[ℚ] ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  IsAlgClosed.lift

theorem coeffMap_sigma_constants (a : Qbar) :
    coeffMap sigma.toRingHom (algebraMap Qbar (LaurentSeries Qbar) a) =
      algebraMap ℂ (LaurentSeries ℂ) (sigma a) := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
  rfl

theorem coeffMap_sigma_rational (x : LaurentSeries ℚ) :
    coeffMap sigma.toRingHom (coeffEmb Qbar x) = coeffEmb ℂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr sigma.comp_algebraMap x

theorem coeffMap_sigma_mem_original (N : ℕ) {x : LaurentSeries Qbar}
    (hx : x ∈ modularFunctionFieldOver N Qbar) :
    coeffMap sigma.toRingHom x ∈ modularFunctionFieldOver N ℂ := by
  change x ∈ Subfield.closure (Set.range (algebraMap Qbar (LaurentSeries Qbar)) ∪
    (coeffEmb Qbar '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ)))) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
    · rw [coeffMap_sigma_constants]
      exact (modularFunctionFieldOver N ℂ).algebraMap_mem _
    · rw [coeffMap_sigma_rational]
      exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | neg x _ hx => simpa only [map_neg] using neg_mem hx
  | inv x _ hx => simpa only [map_inv₀] using inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

/-- The actual original modular field embedded by its Laurent coefficients. -/
def fieldMap (N : ℕ) : modularFunctionFieldOver N Qbar →+* modularFunctionFieldOver N ℂ where
  toFun x := ⟨coeffMap sigma.toRingHom x.val, coeffMap_sigma_mem_original N x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem fieldMap_constants (N : ℕ) (a : Qbar) :
    fieldMap N (algebraMap Qbar (modularFunctionFieldOver N Qbar) a) =
      algebraMap ℂ (modularFunctionFieldOver N ℂ) (sigma a) :=
  Subtype.ext (coeffMap_sigma_constants a)

theorem fieldMap_j (N : ℕ) : fieldMap N (jOver N Qbar) = jOver N ℂ :=
  Subtype.ext (coeffMap_sigma_rational _)

theorem fieldMap_jN (N : ℕ) [NeZero N] : fieldMap N (jNOver N Qbar) = jNOver N ℂ :=
  Subtype.ext (coeffMap_sigma_rational _)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
