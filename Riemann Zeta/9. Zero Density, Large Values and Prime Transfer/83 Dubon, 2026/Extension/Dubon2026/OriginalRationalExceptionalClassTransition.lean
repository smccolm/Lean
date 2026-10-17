import Dubon2026.OriginalClassesModOutsideBaseChange
import Dubon2026.ArithmeticExceptionalSUnitSupport

/-! # Actual exceptional-support class transition in the rational tower

The exceptional support is the literal set of primes containing the same
rational integer. Its pullback equality is proved from the scalar tower.
The existing outside-unit quotient map therefore supplies DUB-17's stage
transition without a support or coefficient-comparison premise.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra ℚ E] [Algebra ℚ L] [Algebra E L] [IsScalarTower ℚ E L] [IsGalois ℚ E]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

omit [IsGalois ℚ E] in
/-- The same rational exceptional integer defines the actual pulled-back
finite-prime supports. -/
theorem originalRationalExceptionalSupport_tower
    (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ originalExceptionalIntegerSupport L (algebraMap (𝓞 ℚ) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha) ↔
      originalFinitePrimeBelow E L w ∈
        originalExceptionalIntegerSupport E (algebraMap (𝓞 ℚ) (𝓞 E) a)
          (originalIntegerMap_ne_zero (L := E) a ha) := by
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  change algebraMap (𝓞 ℚ) (𝓞 L) a ∈ w.asIdeal ↔
    algebraMap (𝓞 E) (𝓞 L) (algebraMap (𝓞 ℚ) (𝓞 E) a) ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 E) (𝓞 L)]

/-- The original outside-unit class quotient transition at the same
rational exceptional support. -/
def originalRationalExceptionalClassTransition :
    Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/ℚ) →* Gal(E/ℚ))
      (originalIdeleClassesModOutsideRep ℚ E
        (originalExceptionalIntegerSupport E (algebraMap (𝓞 ℚ) (𝓞 E) a)
          (originalIntegerMap_ne_zero (L := E) a ha))
        (originalExceptionalIntegerSupport_galoisStable E ℚ a ha)) ⟶
    originalIdeleClassesModOutsideRep ℚ L
      (originalExceptionalIntegerSupport L (algebraMap (𝓞 ℚ) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha))
      (originalExceptionalIntegerSupport_galoisStable L ℚ a ha) :=
  originalClassesModOutsideBaseChangeRepHom ℚ E L _ _ _ _
    (originalRationalExceptionalSupport_tower E L a ha)

end
end Dubon2026
