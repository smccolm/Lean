import Dubon2026.OriginalClassQuotientNormalInvariants
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # Actual arithmetic finite normal invariants retain their fixed-field classes

The same exceptional integer gives the pulled-back fixed-field support.
Original arithmetic unramifiedness supplies the invariant-descent premise.
The coefficient comparison and H2 comparison therefore concern the actual
normal quotient action, an input to P-class-formation H2 normalization on
DUB-17's global duality and arithmetic patching route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union carries its literal rational inclusion. -/
local instance normalClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The original finite stage has its literal rational algebra. -/
local instance normalClassStageAlgebra : Algebra ℚ F := F.algebra'
/-- The actual finite arithmetic stage is a number field. -/
local instance normalClassStageNumberField : NumberField F := NumberField.of_module_finite ℚ F

variable (H : Subgroup Gal(F/ℚ)) [H.Normal]

/-- The actual fixed field carries its original rational subfield algebra. -/
local instance normalClassFixedAlgebra : Algebra ℚ (IntermediateField.fixedField H) :=
  (IntermediateField.fixedField H).algebra'

/-- The same exceptional integer specifies the actual fixed-field support. -/
abbrev rationalArithmeticNormalClassSupport :=
  originalExceptionalIntegerSupport (IntermediateField.fixedField H)
    (algebraMap (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H)) a)
    (originalIntegerMap_ne_zero (L := IntermediateField.fixedField H) a ha)

omit [H.Normal] in
/-- The actual finite arithmetic support is precisely the pullback of the fixed-field support. -/
theorem rationalArithmeticNormalClassSupport_pullback
    (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ arithmeticSUnitFiniteStageSupport ℚ Ω a ha F ↔
      originalFinitePrimeBelow (IntermediateField.fixedField H) F w ∈
        rationalArithmeticNormalClassSupport Ω a ha F H := by
  change w ∈ originalExceptionalIntegerSupport F _ _ ↔
    originalFinitePrimeBelow (IntermediateField.fixedField H) F w ∈ originalExceptionalIntegerSupport _ _ _
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  change algebraMap (𝓞 ℚ) (𝓞 F) a ∈ w.asIdeal ↔
    algebraMap (𝓞 (IntermediateField.fixedField H)) (𝓞 F)
      (algebraMap (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H)) a) ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H)) (𝓞 F)]

/-- The actual fixed-field class quotient coefficient with its original rational Galois action. -/
abbrev rationalArithmeticNormalClassRep :=
  originalIdeleClassesModOutsideRep ℚ (IntermediateField.fixedField H)
    (rationalArithmeticNormalClassSupport Ω a ha F H)
    (originalExceptionalIntegerSupport_galoisStable (IntermediateField.fixedField H) ℚ a ha)

/-- The original arithmetic normal invariant coefficient is the actual fixed-field class quotient. -/
def rationalArithmeticClassNormalInvariantCoefficientIso :
    Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (rationalArithmeticNormalClassRep Ω a ha F H) ≅
      (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).quotientToInvariants H :=
  originalClassQuotientNormalInvariantCoefficientIso ℚ F H _ _ _ _
    (rationalArithmeticNormalClassSupport_pullback Ω a ha F H)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

/-- H2 of the original arithmetic normal invariant module equals H2 of its actual fixed-field classes. -/
def rationalArithmeticClassNormalInvariantH2Iso :
    groupCohomology (rationalArithmeticNormalClassRep Ω a ha F H) 2 ≅
      groupCohomology ((arithmeticClassesModOutsideStageRep ℚ Ω a ha F).quotientToInvariants H) 2 :=
  originalClassQuotientNormalInvariantH2Iso ℚ F H _ _ _ _
    (rationalArithmeticNormalClassSupport_pullback Ω a ha F H)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

end
end Dubon2026
