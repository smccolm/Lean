import Dubon2026.FiniteBaseQuadraticComponent
import Dubon2026.ArithmeticRealH2Restriction
import Mathlib.NumberTheory.NumberField.CMField

/-! The original real-place conjugation fixes the totally real finite base.
It therefore gives an actual arithmetic involution in the source base-field
Galois group, needed for the polarized CM residual construction in DUB-17. -/

namespace Dubon2026
open NumberField
open scoped NumberField
noncomputable section

/-- Retain the actual rational algebra on the original arithmetic extension. -/
local instance finiteBaseRealUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]

/-- The original real-place conjugation as an element of the actual finite-base arithmetic group. -/
def finiteBaseRealConjugation : finiteBaseArithmeticGaloisGroup a F := by
  refine ⟨rationalRealArithmeticRestriction a Complex.conjAe, ?_⟩
  change (show Gal(rationalUnramifiedExtension a / ℚ) from
    rationalRealArithmeticRestriction a Complex.conjAe) ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let φ : F →+* ℂ := ((rationalArithmeticLocalEmbedding (K := ℂ) a).comp F.val).toRingHom
  apply (rationalArithmeticLocalEmbedding (K := ℂ) a).injective
  exact (rationalArithmeticLocalRestrictionContinuous_commutes (F := ℝ) (K := ℂ)
    a Complex.conjAe x).trans
      (RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal φ) ⟨x, hx⟩)

/-- The original arithmetic involution acts by actual complex conjugation through the same embedding. -/
theorem finiteBaseRealConjugation_commutes (x : rationalUnramifiedExtension a) :
    rationalArithmeticLocalEmbedding (K := ℂ) a
        (finiteBaseArithmeticGaloisEquiv a F (finiteBaseRealConjugation a F) x) =
      Complex.conjAe (rationalArithmeticLocalEmbedding (K := ℂ) a x) :=
  rationalArithmeticLocalRestrictionContinuous_commutes (F := ℝ) (K := ℂ) a Complex.conjAe x

/-- The original real-place arithmetic conjugation squares to the identity. -/
theorem finiteBaseRealConjugation_mul_self :
    finiteBaseRealConjugation a F * finiteBaseRealConjugation a F = 1 := by
  have hj : Complex.conjAe * Complex.conjAe = 1 := by
    ext z
    simp
  apply Subtype.ext
  change rationalRealArithmeticRestriction a Complex.conjAe *
    rationalRealArithmeticRestriction a Complex.conjAe = 1
  rw [← map_mul, hj, map_one]

end
end Dubon2026
