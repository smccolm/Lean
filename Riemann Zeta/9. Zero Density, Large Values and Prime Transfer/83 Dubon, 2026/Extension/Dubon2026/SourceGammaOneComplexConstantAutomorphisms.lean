import Dubon2026.SourceGammaOneExtendedPlaceMap
import Dubon2026.SourceOriginalComplexConstantAutomorphisms
import Dubon2026.SourceGammaOneArithmeticPicard

/-! DUB-17/18 -> original arithmetic torsion comparison -> finite torsion
descent. The repo's existing coefficient action already acts on original
fields, places, divisors and Picard groups. Restrict a Qbar-linear automorphism
of the complex constants to Q, then prove it fixes every original arithmetic
function and every lifted arithmetic place. This avoids introducing the
external general semilinear-automorphism framework.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra

variable (N : ℕ) [NeZero N]
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar

omit [NeZero N] in
theorem complexAut_fixes_arithmetic (τ : ℂ ≃ₐ[Qbar] ℂ) (f : FQ) :
    arithmeticRingAut (Gamma1 N) (OriginalConstantField.complexAutRestrict τ) (fieldMap N f) = fieldMap N f := by
  apply Subtype.ext
  ext k
  change τ (OriginalConstantField.sigma (f.val.coeff k)) = OriginalConstantField.sigma (f.val.coeff k)
  exact τ.commutes (f.val.coeff k)

theorem complexAut_fixes_liftPlace (τ : ℂ ≃ₐ[Qbar] ℂ) (P : Place Qbar FQ) :
    arithmeticPlace (Gamma1 N) (OriginalConstantField.complexAutRestrict τ) (liftPlace N P) = liftPlace N P := by
  apply liftPlace_unique N
  ext x
  change arithmeticRingAut (Gamma1 N) (OriginalConstantField.complexAutRestrict τ).symm (fieldMap N x) ∈
    (liftPlace N P).toValuationSubring ↔ x ∈ P.toValuationSubring
  rw [← OriginalConstantField.complexAutRestrict_symm, complexAut_fixes_arithmetic, mem_liftPlace_iff]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
