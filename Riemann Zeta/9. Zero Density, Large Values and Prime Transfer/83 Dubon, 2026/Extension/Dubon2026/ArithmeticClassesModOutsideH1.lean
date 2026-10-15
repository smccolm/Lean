import Dubon2026.OriginalClassesModOutsideH1
import Dubon2026.ArithmeticClassesModOutsideStages

/-! # Original arithmetic class-quotient H1 vanishing

At the fixed exceptional integer over Q, unramifiedness is derived from
membership in the actual arithmetic union. This removes the support
vanishing premise from the finite-stage first class-formation input.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance classFiniteH1UnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable
  (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance classFiniteH1StageAlgebra : Algebra ℚ F := F.algebra'
/-- The original finite arithmetic extension is a number field. -/
local instance classFiniteH1StageNumberField : NumberField F := NumberField.of_module_finite ℚ F

/-- Every actual finite arithmetic stage is absolutely unramified outside the unchanged exceptional support. -/
theorem rationalArithmeticFiniteStage_outside_unramified
    (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ arithmeticSUnitFiniteStageSupport ℚ Ω a ha F) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  have hwa : algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal := by
    simpa only [arithmeticSUnitFiniteStageSupport, mem_originalExceptionalIntegerSupport] using hw
  have hi := originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField w hwa
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ) (p := w.asIdeal) w.ne_bot).mpr hi
  haveI : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv
      (show ℤ ≃ₐ[ℤ] 𝓞 ℚ from { Rat.ringOfIntegersEquiv.symm with
        commutes' := fun r => map_intCast Rat.ringOfIntegersEquiv.symm r })
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime w.asIdeal)

/-- H1 of the literal class quotient vanishes at every actual rational arithmetic stage. -/
theorem rationalArithmeticClassesModOutsideStage_first_zero :
    Limits.IsZero (groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 1) :=
  originalClassesModOutside_first_zero ℚ F _ _
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

end
end Dubon2026
