import Dubon2026.SourceGammaOneFunctionFieldBaseChange
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> arithmetic and complex comparison of the actual Hecke maps.
Coefficient transport preserves the same rational integral-ratio field.
This one map serves both arithmetic automorphisms and the fixed Qbar-to-C
embedding, using the existing Laurent coefficient composition theorem. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField
open scoped MatrixGroups
variable {L L' : Type*} [Field L] [Field L'] [Algebra ℚ L] [Algebra ℚ L']

private theorem coeffMap_constants (σ : L →ₐ[ℚ] L') (a : L) :
    coeffMap σ.toRingHom (algebraMap L (LaurentSeries L) a) =
      algebraMap L' (LaurentSeries L') (σ a) := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
  rfl

private theorem coeffMap_rational (σ : L →ₐ[ℚ] L') (x : LaurentSeries ℚ) :
    coeffMap σ.toRingHom (coeffEmb L x) = coeffEmb L' x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr σ.comp_algebraMap x

theorem coeffMap_mem_functionFieldOver
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L →ₐ[ℚ] L')
    {x : LaurentSeries L} (hx : x ∈ functionFieldOver Γ L) :
    coeffMap σ.toRingHom x ∈ functionFieldOver Γ L' := by
  change x ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
    (coeffEmb L '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ)))) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
    · rw [coeffMap_constants]
      exact (functionFieldOver Γ L').algebraMap_mem _
    · rw [coeffMap_rational]
      exact coeffEmb_mem_laurentBaseChange L' hz
  | one => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | neg x _ hx => simpa only [map_neg] using neg_mem hx
  | inv x _ hx => simpa only [map_inv₀] using inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

/-- The actual coefficient homomorphism on the scalar-extended modular integral-ratio field. -/
def fieldCoefficientMap (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ : L →ₐ[ℚ] L') : functionFieldOver Γ L →+* functionFieldOver Γ L' where
  toFun x := ⟨coeffMap σ.toRingHom x.val, coeffMap_mem_functionFieldOver Γ σ x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem fieldCoefficientMap_coe
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L →ₐ[ℚ] L')
    (x : functionFieldOver Γ L) :
    (fieldCoefficientMap Γ σ x : LaurentSeries L') = coeffMap σ.toRingHom x.val := rfl

theorem fieldCoefficientMap_constants
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L →ₐ[ℚ] L') (a : L) :
    fieldCoefficientMap Γ σ (algebraMap L (functionFieldOver Γ L) a) =
      algebraMap L' (functionFieldOver Γ L') (σ a) :=
  Subtype.ext (coeffMap_constants σ a)

theorem fieldCoefficientMap_j
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (σ : L →ₐ[ℚ] L') :
    fieldCoefficientMap Γ σ (jCoordinateOver Γ L) = jCoordinateOver Γ L' :=
  Subtype.ext (coeffMap_rational σ _)

end
end Dubon2026.SourceFunctionField.GammaOne
