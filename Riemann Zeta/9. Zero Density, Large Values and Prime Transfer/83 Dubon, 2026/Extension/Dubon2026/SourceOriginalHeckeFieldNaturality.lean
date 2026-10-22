import Dubon2026.SourceOriginalHeckeDegeneracy
import Dubon2026.SourceOriginalArithmeticFieldAction
import Dubon2026.SourceOriginalComplexCoefficientMap

/-! DUB-17/18 -> original Tate Hecke realization -> the original Picard
correspondence and arithmetic-to-complex comparison. Both literal
degeneracy maps commute with the actual arithmetic coefficient action and
the fixed embedding of the original algebraic closure into the complex
numbers. These field identities will supply the divisor comparison; they
do not by themselves assert Picard or period equivariance.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L]

theorem originalHeckeAlpha_arithmetic (N ℓ : ℕ) (σ : L ≃ₐ[ℚ] L)
    (x : modularFunctionFieldOver N L) :
    originalArithmeticRingAut (N * ℓ) σ (originalHeckeAlpha L N ℓ x) =
      originalHeckeAlpha L N ℓ (originalArithmeticRingAut N σ x) := by
  apply Subtype.ext
  change coeffMap σ.toRingHom (originalHeckeAlpha L N ℓ x : LaurentSeries L) =
    (originalHeckeAlpha L N ℓ (originalArithmeticRingAut N σ x) : LaurentSeries L)
  rw [originalHeckeAlpha_coe, originalHeckeAlpha_coe]
  rfl

theorem originalHeckeBeta_arithmetic (N ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L)
    (x : modularFunctionFieldOver N L) :
    originalArithmeticRingAut (N * ℓ) σ (originalHeckeBeta L N ℓ x) =
      originalHeckeBeta L N ℓ (originalArithmeticRingAut N σ x) :=
  Subtype.ext (coeffMap_qExpand σ.toRingHom ℓ x.val)

namespace OriginalConstantField
local notation "Qbar" => AlgebraicClosure ℚ

theorem originalHeckeAlpha_fieldMap (N ℓ : ℕ) (x : modularFunctionFieldOver N Qbar) :
    fieldMap (N * ℓ) (originalHeckeAlpha Qbar N ℓ x) =
      originalHeckeAlpha ℂ N ℓ (fieldMap N x) := by
  apply Subtype.ext
  change coeffMap sigma.toRingHom (originalHeckeAlpha Qbar N ℓ x : LaurentSeries Qbar) =
    (originalHeckeAlpha ℂ N ℓ (fieldMap N x) : LaurentSeries ℂ)
  rw [originalHeckeAlpha_coe, originalHeckeAlpha_coe]
  rfl

theorem originalHeckeBeta_fieldMap (N ℓ : ℕ) [NeZero ℓ]
    (x : modularFunctionFieldOver N Qbar) :
    fieldMap (N * ℓ) (originalHeckeBeta Qbar N ℓ x) =
      originalHeckeBeta ℂ N ℓ (fieldMap N x) :=
  Subtype.ext (coeffMap_qExpand sigma.toRingHom ℓ x.val)

end OriginalConstantField
end
end Dubon2026.SourceFunctionField
