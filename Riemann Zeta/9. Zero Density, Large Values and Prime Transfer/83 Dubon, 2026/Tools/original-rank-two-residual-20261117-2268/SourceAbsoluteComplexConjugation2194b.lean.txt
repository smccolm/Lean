import Dubon2026.SourceAbsoluteCyclotomicCharacter
import Dubon2026.EmbeddedNormalGaloisRestriction
import Dubon2026.CyclotomicConjugationPower
import Dubon2026.SourceRationalLocalValuation

/-! DUB-17/18 -> actual rank-two realization -> original odd involution.
Reuse the normal-embedding restriction and native complex conjugation.
Its actual cyclotomic exponent is minus one, linking the original
arithmetic group to the trace-algebra idempotent construction. -/
namespace Dubon2026
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- Actual complex conjugation on the original rational algebraic closure,
through the specified original complex embedding. -/
def sourceAbsoluteComplexConjugation (e : Qbar →ₐ[ℚ] ℂ) : Qbar ≃ₐ[ℚ] Qbar :=
  embeddedNormalGaloisRestriction e (Complex.conjAe.restrictScalars ℚ)

/-- The constructed restriction acts as actual complex conjugation. -/
theorem sourceAbsoluteComplexConjugation_isConj (e : Qbar →ₐ[ℚ] ℂ) :
    NumberField.ComplexEmbedding.IsConj e.toRingHom (sourceAbsoluteComplexConjugation e) := by
  ext x
  exact (embeddedNormalGaloisRestriction_commutes e (Complex.conjAe.restrictScalars ℚ) x).symm

/-- The original conjugation is an involution on the same absolute group. -/
theorem sourceAbsoluteComplexConjugation_sq (e : Qbar →ₐ[ℚ] ℂ) :
    sourceAbsoluteComplexConjugation e * sourceAbsoluteComplexConjugation e = 1 := by
  ext x
  exact NumberField.ComplexEmbedding.isConj_apply_apply (sourceAbsoluteComplexConjugation_isConj e) x

/-- At every original finite precision, actual complex conjugation has the
same cyclotomic exponent minus one. -/
theorem sourceAbsoluteCyclotomicCharacter_conjugation (N : ℕ) [NeZero N]
    (e : Qbar →ₐ[ℚ] ℂ) :
    sourceAbsoluteCyclotomicCharacter N (sourceAbsoluteComplexConjugation e) = -1 := by
  have hx : ∃ ζ : Qbar, IsPrimitiveRoot ζ N :=
    HasEnoughRootsOfUnity.exists_primitiveRoot Qbar N
  exact originalCyclotomicConjugation_power (Classical.choose_spec hx) e.toRingHom
    (sourceAbsoluteComplexConjugation e) (sourceAbsoluteComplexConjugation_isConj e)

end
end Dubon2026
