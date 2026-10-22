import Dubon2026.SourceOriginalExtendedPlaceMap
import Dubon2026.SourceOriginalArithmeticPicard

/-! DUB-17/18 -> original arithmetic torsion comparison -> finite torsion
descent. The repo's existing coefficient action already acts on original
fields, places, divisors and Picard groups. Restrict a Qbar-linear automorphism
of the complex constants to Q, then prove it fixes every original arithmetic
function and every lifted arithmetic place. This avoids introducing the
external general semilinear-automorphism framework.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra

/-- Restriction of an actual complex constant automorphism from Qbar to Q. -/
def complexAutRestrict : (ℂ ≃ₐ[Qbar] ℂ) →* (ℂ ≃ₐ[ℚ] ℂ) where
  toFun τ := { τ.toRingEquiv with
    commutes' q := by
      have hq : algebraMap ℚ ℂ q = sigma (algebraMap ℚ Qbar q) := (sigma.commutes q).symm
      change τ (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q
      rw [hq]
      exact τ.commutes (algebraMap ℚ Qbar q) }
  map_one' := by ext x; rfl
  map_mul' τ υ := by ext x; rfl

theorem complexAutRestrict_symm (τ : ℂ ≃ₐ[Qbar] ℂ) :
    complexAutRestrict τ.symm = (complexAutRestrict τ).symm := by
  ext x
  rfl

variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar

omit [NeZero N] in
theorem complexAut_fixes_arithmetic (τ : ℂ ≃ₐ[Qbar] ℂ) (f : FQ) :
    originalArithmeticRingAut N (complexAutRestrict τ) (fieldMap N f) = fieldMap N f := by
  apply Subtype.ext
  ext k
  change τ (sigma (f.val.coeff k)) = sigma (f.val.coeff k)
  exact τ.commutes (f.val.coeff k)

theorem complexAut_fixes_liftPlace (τ : ℂ ≃ₐ[Qbar] ℂ) (P : Place Qbar FQ) :
    originalArithmeticPlace N (complexAutRestrict τ) (liftPlace N P) = liftPlace N P := by
  apply liftPlace_unique N
  ext x
  change originalArithmeticRingAut N (complexAutRestrict τ).symm (fieldMap N x) ∈
    (liftPlace N P).toValuationSubring ↔ x ∈ P.toValuationSubring
  rw [← complexAutRestrict_symm, complexAut_fixes_arithmetic, mem_liftPlace_iff]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
