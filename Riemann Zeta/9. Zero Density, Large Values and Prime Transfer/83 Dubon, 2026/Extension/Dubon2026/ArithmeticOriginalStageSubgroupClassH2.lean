import Dubon2026.ArithmeticOriginalStageClassColimit
import Dubon2026.OriginalClassQuotientSubgroupCohomology
import Dubon2026.OriginalClassesModOutsideH2Comparison

/-! # The scalar-stage subgroup obstruction in actual fixed-field class H2

The original stage's unramifiedness supplies the outside-unit vanishing
conditions. The existing quotient and fixed-field cohomology isomorphisms
then identify the literal restricted coefficient with full idele classes.
For the coefficient prime's Sylow subgroup this is the prime-power class
group needed for DUB-17's remaining local normalization comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the displayed rational structure of each original finite stage. -/
local instance originalStageSubgroupFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)

/-- The original scalar stage is absolutely unramified outside its actual
exceptional support, by its defining ramification-index property. -/
theorem arithmeticOriginalStage_outside_unramified
    (w : HeightOneSpectrum (𝓞 L.val))
    (hw : w ∉ originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
      (originalIntegerMap_ne_zero (L := L.val) a ha)) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  have hwa : algebraMap (𝓞 ℚ) (𝓞 L.val) a ∉ w.asIdeal := by
    simpa only [mem_originalExceptionalIntegerSupport] using hw
  have hi := L.property w hwa
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ) (p := w.asIdeal) w.ne_bot).mpr hi
  haveI : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv
      (show ℤ ≃ₐ[ℤ] 𝓞 ℚ from { Rat.ringOfIntegersEquiv.symm with
        commutes' := fun r => map_intCast Rat.ringOfIntegersEquiv.symm r })
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime w.asIdeal)

/-- Original full-class H2 over the subgroup's actual fixed field equals
H2 of the scalar-stage quotient restricted to that same subgroup. -/
def arithmeticOriginalStageSubgroupClassH2Iso (S : Subgroup Gal(L.val/ℚ)) :
    groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L.val) 2 ≅
      groupCohomology (Rep.res S.subtype (arithmeticOriginalStageClassRep Ω a ha L)) 2 := by
  let T := originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
    (originalIntegerMap_ne_zero (L := L.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha
  exact originalClassesModOutsideH2Iso (IntermediateField.fixedField S) L.val T
      (originalClassQuotient_fixedField_support ℚ L.val T hT S)
      (arithmeticOriginalStage_outside_unramified Ω a ha L) ≪≫
    originalClassQuotientSubgroupCohomologyIso ℚ L.val T hT S 2

end
end Dubon2026
