import Dubon2026.RationalArithmeticOpenQuotientClassInvariants
import Dubon2026.OriginalClassesModOutsideH2Comparison

/-! # Original open-quotient H2 has genuine full-class representatives

Arithmetic membership supplies absolute unramifiedness of the genuine
fixed field. The proved outside-unit comparison and actual quotient-action
isomorphism then transfer full-class H2 to the original finite quotient.
This removes a coefficient/cohomology premise for DUB-17's class-formation
normalization, without asserting an invariant map or exact group order.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union retains its rational inclusion. -/
local instance relativeH2ClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'
/-- The original arithmetic union is Galois. -/
local instance relativeH2ClassUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (U V : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
  [hVU : Fact (V.toSubgroup ≤ U.toSubgroup)]
  [(V.toSubgroup.subgroupOf U.toSubgroup).Normal]

/-- The lower fixed field has its literal rational algebra. -/
local instance relativeH2ClassLowerAlgebra : Algebra ℚ (IntermediateField.fixedField U.toSubgroup) :=
  (IntermediateField.fixedField U.toSubgroup).algebra'
/-- The upper fixed field has its literal rational algebra. -/
local instance relativeH2ClassUpperAlgebra : Algebra ℚ (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.fixedField V.toSubgroup).algebra'
/-- The lower rational action is induced by the original algebra. -/
local instance relativeH2ClassLowerRatSMul : SMul ℚ (IntermediateField.fixedField U.toSubgroup) :=
  Algebra.toSMul
/-- The upper rational action is induced by the original algebra. -/
local instance relativeH2ClassUpperRatSMul : SMul ℚ (IntermediateField.fixedField V.toSubgroup) :=
  Algebra.toSMul
/-- The lower fixed field is finite over the rationals. -/
local instance relativeH2ClassLowerFinite : FiniteDimensional ℚ (IntermediateField.fixedField U.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite U
/-- The upper fixed field is finite over the rationals. -/
local instance relativeH2ClassUpperFinite : FiniteDimensional ℚ (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite V
/-- The lower fixed field is an actual number field. -/
local instance relativeH2ClassLowerNumberField : NumberField (IntermediateField.fixedField U.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- The upper fixed field is an actual number field. -/
local instance relativeH2ClassUpperNumberField : NumberField (IntermediateField.fixedField V.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- Containment gives the literal relative fixed-field algebra. -/
local instance relativeH2ClassAlgebra : Algebra (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.inclusion (IntermediateField.fixedField_le hVU.out)).toAlgebra
/-- The relative module uses the original field inclusion. -/
local instance relativeH2ClassModule : Module (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toModule
/-- The relative scalar action uses the original inclusion. -/
local instance relativeH2ClassSMul : SMul (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toSMul
/-- The relative multiplicative action is induced by the original module. -/
local instance relativeH2ClassMulAction : MulAction (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (relativeH2ClassModule Ω a U V).toDistribMulAction.toMulAction
/-- The relative fixed-field inclusion forms the original rational tower. -/
local instance relativeH2ClassTower : IsScalarTower ℚ (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := .of_algebraMap_eq' rfl
/-- Normality gives the genuine relative fixed-field Galois extension. -/
local instance relativeH2ClassGalois : IsGalois (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_relative_isGalois U V hVU.out

omit hVU [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] in
/-- The genuine open-subgroup fixed field is absolutely unramified outside its original support. -/
theorem rationalArithmeticOpenFixedField_outside_unramified
    (w : HeightOneSpectrum (𝓞 (IntermediateField.fixedField V.toSubgroup)))
    (hw : w ∉ rationalArithmeticOpenBaseClassSupport Ω a ha V) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  let E := IntermediateField.fixedField V.toSubgroup
  have hwa : algebraMap (𝓞 ℚ) (𝓞 E) a ∉ w.asIdeal := by
    simpa only [rationalArithmeticOpenBaseClassSupport, mem_originalExceptionalIntegerSupport] using hw
  have hi := originalUnramifiedUnion_finite_ramification a ha E w hwa
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 ℚ) (p := w.asIdeal) w.ne_bot).mpr hi
  haveI : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv
      (show ℤ ≃ₐ[ℤ] 𝓞 ℚ from { Rat.ringOfIntegersEquiv.symm with
        commutes' := fun r => map_intCast Rat.ringOfIntegersEquiv.symm r })
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime w.asIdeal)

/-- The actual relative fixed-field extension is finite. -/
local instance relativeH2ClassFinite : FiniteDimensional (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  FiniteDimensional.right ℚ _ _

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- H2 of the original open quotient invariants is the genuine relative full-class H2. -/
def rationalArithmeticFullClassToOpenQuotientH2Iso :
    groupCohomology (originalIdeleClassRep (IntermediateField.fixedField U.toSubgroup)
      (IntermediateField.fixedField V.toSubgroup)) 2 ≅
      groupCohomology
        ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
          (V.toSubgroup.subgroupOf U.toSubgroup)) 2 :=
  originalClassesModOutsideH2Iso (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup)
    (rationalArithmeticOpenBaseClassSupport Ω a ha V)
    (rationalArithmeticRelativeClassSupport_stable Ω a ha U V)
    (rationalArithmeticOpenFixedField_outside_unramified Ω a ha V) ≪≫
      rationalArithmeticOpenQuotientClassH2Iso Ω a ha U V

/-- Every original open-quotient H2 class has a unique genuine relative full-class preimage. -/
theorem rationalArithmeticOpenQuotientH2_unique_full_class
    (x : groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) :
    ∃! y : groupCohomology (originalIdeleClassRep (IntermediateField.fixedField U.toSubgroup)
      (IntermediateField.fixedField V.toSubgroup)) 2,
      (rationalArithmeticFullClassToOpenQuotientH2Iso Ω a ha U V).hom y = x :=
  (rationalArithmeticFullClassToOpenQuotientH2Iso Ω a ha U V).toLinearEquiv.bijective.existsUnique x

/-- Original open-quotient H2 is finite with order dividing the actual subgroup index. -/
theorem rationalArithmeticOpenQuotientH2_finite_card_dvd :
    Finite (groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) ∧
    Nat.card (groupCohomology
      ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup)) 2) ∣
      Nat.card (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) := by
  let e := (rationalArithmeticFullClassToOpenQuotientH2Iso Ω a ha U V).toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd
    (IntermediateField.fixedField U.toSubgroup) (IntermediateField.fixedField V.toSubgroup)
  haveI := hf
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e, openGaloisSubgroupRelativeQuotient_degree U V hVU.out]
  exact hd

end
end Dubon2026
