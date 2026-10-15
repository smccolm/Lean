import Dubon2026.RationalArithmeticRelativeClassAction
import Dubon2026.OriginalClassQuotientNormalInvariants

/-! # Genuine relative fixed-field classes are the original quotient invariant representation

Literal arithmetic class inclusions preserve the original quotient action.
The existing invariant bijection now identifies the actual representation,
and hence H2, needed for DUB-17's P-class-formation normalization. The
normalized invariant maps and Ext/localization comparison remain open.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union retains its rational inclusion. -/
local instance quotientClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'
/-- The original arithmetic union is Galois. -/
local instance quotientClassUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (U V : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
  [hVU : Fact (V.toSubgroup ≤ U.toSubgroup)]
  [(V.toSubgroup.subgroupOf U.toSubgroup).Normal]

/-- The lower fixed field has its literal rational algebra. -/
local instance quotientClassLowerAlgebra : Algebra ℚ (IntermediateField.fixedField U.toSubgroup) :=
  (IntermediateField.fixedField U.toSubgroup).algebra'
/-- The upper fixed field has its literal rational algebra. -/
local instance quotientClassUpperAlgebra : Algebra ℚ (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.fixedField V.toSubgroup).algebra'
/-- The lower rational action is induced by the original algebra. -/
local instance quotientClassLowerRatSMul : SMul ℚ (IntermediateField.fixedField U.toSubgroup) :=
  Algebra.toSMul
/-- The upper rational action is induced by the original algebra. -/
local instance quotientClassUpperRatSMul : SMul ℚ (IntermediateField.fixedField V.toSubgroup) :=
  Algebra.toSMul
/-- The lower fixed field is finite over the rationals. -/
local instance quotientClassLowerFinite : FiniteDimensional ℚ (IntermediateField.fixedField U.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite U
/-- The upper fixed field is finite over the rationals. -/
local instance quotientClassUpperFinite : FiniteDimensional ℚ (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite V
/-- The lower fixed field is an actual number field. -/
local instance quotientClassLowerNumberField : NumberField (IntermediateField.fixedField U.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- The upper fixed field is an actual number field. -/
local instance quotientClassUpperNumberField : NumberField (IntermediateField.fixedField V.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- Containment gives the literal relative fixed-field algebra. -/
local instance quotientClassAlgebra : Algebra (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.inclusion (IntermediateField.fixedField_le hVU.out)).toAlgebra
/-- The relative module uses the original field inclusion. -/
local instance quotientClassModule : Module (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toModule
/-- The relative scalar action uses the original inclusion. -/
local instance quotientClassSMul : SMul (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toSMul
/-- The relative multiplicative action is induced by the original module. -/
local instance quotientClassMulAction : MulAction (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (quotientClassModule Ω a U V).toDistribMulAction.toMulAction
/-- The relative fixed-field inclusion forms the original rational tower. -/
local instance quotientClassTower : IsScalarTower ℚ (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := .of_algebraMap_eq' rfl
/-- Normality gives the genuine relative fixed-field Galois extension. -/
local instance quotientClassGalois : IsGalois (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_relative_isGalois U V hVU.out

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Genuine relative fixed-field classes map equivariantly to the original quotient invariant coefficient. -/
def rationalArithmeticOpenQuotientClassInclusion :
    Rep.res (openGaloisSubgroupRelativeQuotientEquiv U V hVU.out).toMonoidHom
      (rationalArithmeticRelativeClassRep Ω a ha U V) ⟶
      (Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup) := by
  refine Rep.ofHom ⟨(rationalArithmeticOpenBaseClassToColimit Ω a ha V).codRestrict _
    (fun c s => ?_), fun q => ?_⟩
  · exact rationalArithmeticOpenBaseClassToColimit_fixed Ω a ha V c ⟨s.val.val, s.property⟩
  · apply LinearMap.ext
    intro c
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      exact rationalArithmeticOpenBaseClassToColimit_equivariant Ω a ha U V g c

/-- The actual quotient invariant class inclusion has exactly the genuine fixed-field classes as preimages. -/
theorem rationalArithmeticOpenQuotientClassInclusion_bijective :
    Function.Bijective (rationalArithmeticOpenQuotientClassInclusion Ω a ha U V).hom := by
  constructor
  · intro c d h
    exact rationalArithmeticOpenBaseClassToColimit_injective Ω a ha V (congrArg Subtype.val h)
  · intro x
    have hx : ∀ g : V, (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val x.val = x.val := by
      intro g
      exact x.property ⟨⟨g.val, hVU.out g.property⟩, g.property⟩
    have hb := (rationalArithmeticOpenBaseClassToColimitInvariants_bijective Ω a ha V).2 ⟨x.val, hx⟩
    obtain ⟨c, hc⟩ := hb
    have he := congrArg Subtype.val hc
    exact ⟨c, Subtype.ext he⟩

/-- The actual quotient invariant representation is the genuine relative fixed-field class representation. -/
def rationalArithmeticOpenQuotientClassCoefficientIso :
    Rep.res (openGaloisSubgroupRelativeQuotientEquiv U V hVU.out).toMonoidHom
      (rationalArithmeticRelativeClassRep Ω a ha U V) ≅
      (Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
        (V.toSubgroup.subgroupOf U.toSubgroup) := by
  let φ := rationalArithmeticOpenQuotientClassInclusion Ω a ha U V
  have hφ := rationalArithmeticOpenQuotientClassInclusion_bijective Ω a ha U V
  haveI : Mono φ := (Rep.mono_iff_injective _).mpr hφ.1
  haveI : Epi φ := (Rep.epi_iff_surjective _).mpr hφ.2
  haveI : IsIso φ := isIso_of_mono_of_epi _
  exact asIso φ

/-- H2 of the genuine relative fixed-field classes is H2 of the original arithmetic quotient invariant module. -/
def rationalArithmeticOpenQuotientClassH2Iso :
    groupCohomology (rationalArithmeticRelativeClassRep Ω a ha U V) 2 ≅
      groupCohomology
        ((Rep.res U.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).quotientToInvariants
          (V.toSubgroup.subgroupOf U.toSubgroup)) 2 :=
  originalCohomologyReindex _ (openGaloisSubgroupRelativeQuotientEquiv U V hVU.out) 2 ≪≫
    (groupCohomology.functor ℤ (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) 2).mapIso
      (rationalArithmeticOpenQuotientClassCoefficientIso Ω a ha U V)

end
end Dubon2026
