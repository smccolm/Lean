import Dubon2026.SourceOriginalRationalBottomRestriction
import Dubon2026.SourceResidualRealDeterminant
import Dubon2026.SourcePrimitiveWeightParity
import Dubon2026.FiniteBaseRealConjugation

/-! DUB-17/18 -> original polarized symmetric residual representation.
The already proved global cyclotomic determinant computes oddness at the
native real involution directly, avoiding a new comparison of complex embeddings. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Preserve the actual rational scalar structure in the original union. -/
private local instance originalBottomOddUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The original rational bottom field is totally real via its actual equivalence to ℚ. -/
private local instance originalBottomTotallyReal (a : 𝓞 ℚ) :
    IsTotallyReal (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ (rationalUnramifiedExtension a)).symm.toRingEquiv

/-- The original primitive-form weight gives an odd determinant exponent;
no separate even-weight hypothesis is added to the source consumer. -/
theorem original_primitive_determinantExponent_odd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) : Odd (k - 1).toNat := by
  obtain ⟨b, hb⟩ := sourcePrimitive_weight_even f
  refine ⟨(b - 1).toNat, ?_⟩
  omega

/-- The literal native bottom-field real involution has determinant minus
one under the original representation with its proved odd cyclotomic power. -/
theorem original_rational_bottom_odd_of_cyclotomic
    (a : 𝓞 ℚ) (p w : ℕ) [NeZero p] (hpa : (p : 𝓞 ℚ) ∣ a)
    (hw : Odd w) {L : Type} [Field L] [CharP L p] [TopologicalSpace L]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hρ : Continuous ρ)
    (hdet : GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa).toMonoidHom ^ w) :
    (((show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
      (originalRationalBottomRestriction a)) (finiteBaseRealConjugation a ⊥)).val.det = -1 := by
  exact sourceArithmetic_real_det_of_cyclotomic p a hpa w hw ρ hdet

end
end Dubon2026.SourceDickson
