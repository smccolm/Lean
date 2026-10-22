import Dubon2026.SourceOriginalPicardGroup
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> modular residual Galois association -> the arithmetic
action on the original divisor-class group -> the original coefficient
action on its function field. The same rational Laurent generators are
fixed, while constants transform by the given arithmetic automorphism.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_ArithmeticGalois. Existing coefficient
composition and rational-generator invariance supply the action laws.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L]

theorem coeffMap_original_constants (σ : L ≃ₐ[ℚ] L) (a : L) :
    coeffMap (σ : L →+* L) (algebraMap L (LaurentSeries L) a) =
      algebraMap L (LaurentSeries L) (σ a) := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
  rfl

theorem coeffMap_mem_original (N : ℕ) (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : x ∈ modularFunctionFieldOver N L) :
    coeffMap (σ : L →+* L) x ∈ modularFunctionFieldOver N L := by
  change x ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
    (coeffEmb L '' (modularFunctionFieldFull N : Set (LaurentSeries ℚ)))) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
    · rw [coeffMap_original_constants]
      exact (modularFunctionFieldOver N L).algebraMap_mem _
    · rw [coeffMap_coeffEmb]
      exact coeffEmb_mem_laurentBaseChange L hz
  | one => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | neg x _ hx => simpa only [map_neg] using neg_mem hx
  | inv x _ hx => simpa only [map_inv₀] using inv_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

/-- The actual coefficient automorphism restricted to the original modular field. -/
def originalArithmeticRingAut (N : ℕ) (σ : L ≃ₐ[ℚ] L) :
    modularFunctionFieldOver N L ≃+* modularFunctionFieldOver N L where
  toFun x := ⟨coeffMap (σ : L →+* L) x.val, coeffMap_mem_original N σ x.property⟩
  invFun x := ⟨coeffMap (σ.symm : L →+* L) x.val, coeffMap_mem_original N σ.symm x.property⟩
  left_inv x := by
    apply Subtype.ext
    ext n
    exact σ.symm_apply_apply (x.val.coeff n)
  right_inv x := by
    apply Subtype.ext
    ext n
    exact σ.apply_symm_apply (x.val.coeff n)
  map_mul' x y := Subtype.ext (map_mul (coeffMap (σ : L →+* L)) x.val y.val)
  map_add' x y := Subtype.ext (map_add (coeffMap (σ : L →+* L)) x.val y.val)

theorem originalArithmeticRingAut_constants (N : ℕ) (σ : L ≃ₐ[ℚ] L) (a : L) :
    originalArithmeticRingAut N σ (algebraMap L (modularFunctionFieldOver N L) a) =
      algebraMap L (modularFunctionFieldOver N L) (σ a) :=
  Subtype.ext (coeffMap_original_constants σ a)

theorem originalArithmeticRingAut_j (N : ℕ) (σ : L ≃ₐ[ℚ] L) :
    originalArithmeticRingAut N σ (jOver N L) = jOver N L :=
  Subtype.ext (coeffMap_coeffEmb σ _)

end
end Dubon2026.SourceFunctionField
