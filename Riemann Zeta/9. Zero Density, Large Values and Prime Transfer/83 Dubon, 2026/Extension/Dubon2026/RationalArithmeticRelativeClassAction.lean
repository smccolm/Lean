import Dubon2026.RationalArithmeticOpenClassColimitInvariants
import Dubon2026.OpenSubgroupRelativeRestriction

/-! # Original relative fixed-field class actions

The actual fixed-field class map intertwines literal arithmetic restriction.
This supplies the action compatibility for the finite quotient coefficients
in DUB-17's P-class-formation route, before normalized H2 invariant maps,
Ext duality, reverse localization, and arithmetic patching.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union retains its rational inclusion. -/
local instance relativeClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'
/-- The original arithmetic union is Galois. -/
local instance relativeClassUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (U V : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
  [hVU : Fact (V.toSubgroup ≤ U.toSubgroup)]
  [(V.toSubgroup.subgroupOf U.toSubgroup).Normal]

/-- The lower fixed field has its literal rational algebra. -/
local instance relativeClassLowerAlgebra : Algebra ℚ (IntermediateField.fixedField U.toSubgroup) :=
  (IntermediateField.fixedField U.toSubgroup).algebra'
/-- The upper fixed field has its literal rational algebra. -/
local instance relativeClassUpperAlgebra : Algebra ℚ (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.fixedField V.toSubgroup).algebra'
/-- The lower rational action is induced by the original algebra. -/
local instance relativeClassLowerRatSMul : SMul ℚ (IntermediateField.fixedField U.toSubgroup) :=
  Algebra.toSMul
/-- The upper rational action is induced by the original algebra. -/
local instance relativeClassUpperRatSMul : SMul ℚ (IntermediateField.fixedField V.toSubgroup) :=
  Algebra.toSMul
/-- The lower fixed field is finite over the rationals. -/
local instance relativeClassLowerFinite : FiniteDimensional ℚ (IntermediateField.fixedField U.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite U
/-- The upper fixed field is finite over the rationals. -/
local instance relativeClassUpperFinite : FiniteDimensional ℚ (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite V
/-- The lower fixed field is an actual number field. -/
local instance relativeClassLowerNumberField : NumberField (IntermediateField.fixedField U.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- The upper fixed field is an actual number field. -/
local instance relativeClassUpperNumberField : NumberField (IntermediateField.fixedField V.toSubgroup) :=
  NumberField.of_module_finite ℚ _
/-- Containment gives the literal relative fixed-field algebra. -/
local instance relativeClassAlgebra : Algebra (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (IntermediateField.inclusion (IntermediateField.fixedField_le hVU.out)).toAlgebra
/-- The relative module uses the original field inclusion. -/
local instance relativeClassModule : Module (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toModule
/-- The relative scalar action uses the original inclusion. -/
local instance relativeClassSMul : SMul (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := Algebra.toSMul
/-- The relative multiplicative action is induced by the original module. -/
local instance relativeClassMulAction : MulAction (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  (relativeClassModule Ω a U V).toDistribMulAction.toMulAction
/-- The relative fixed-field inclusion forms the original rational tower. -/
local instance relativeClassTower : IsScalarTower ℚ (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) := .of_algebraMap_eq' rfl
/-- Normality gives the genuine relative fixed-field Galois extension. -/
local instance relativeClassGalois : IsGalois (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) :=
  openGaloisSubgroup_fixedField_relative_isGalois U V hVU.out

include hVU in
omit [(V.toSubgroup.subgroupOf U.toSubgroup).Normal] in
/-- The original exceptional support is stable under actual relative fixed-field automorphisms. -/
theorem rationalArithmeticRelativeClassSupport_stable
    (σ : Gal(IntermediateField.fixedField V.toSubgroup / IntermediateField.fixedField U.toSubgroup))
    (v : HeightOneSpectrum (𝓞 (IntermediateField.fixedField V.toSubgroup))) :
    v ∈ rationalArithmeticOpenBaseClassSupport Ω a ha V ↔
      numberFieldGaloisPlaceEquiv (IntermediateField.fixedField U.toSubgroup)
        (IntermediateField.fixedField V.toSubgroup) σ v ∈
          rationalArithmeticOpenBaseClassSupport Ω a ha V :=
  originalExceptionalIntegerSupport_galoisStable (IntermediateField.fixedField V.toSubgroup)
    ℚ a ha (σ.restrictScalars ℚ) v

/-- Genuine fixed-field classes with their actual relative Galois action. -/
abbrev rationalArithmeticRelativeClassRep :=
  originalIdeleClassesModOutsideRep (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup)
    (rationalArithmeticOpenBaseClassSupport Ω a ha V)
    (rationalArithmeticRelativeClassSupport_stable Ω a ha U V)

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  [hF : Fact (IntermediateField.fixedField V.toSubgroup ≤ F.toIntermediateField)]

/-- The original arithmetic stage has its rational inclusion. -/
local instance relativeClassStageAlgebra : Algebra ℚ F := F.algebra'
/-- Rational scalars on the stage use the original algebra. -/
local instance relativeClassStageRatSMul : SMul ℚ F := Algebra.toSMul
/-- The actual arithmetic stage is a number field. -/
local instance relativeClassStageNumberField : NumberField F := NumberField.of_module_finite ℚ F
/-- The original upper fixed-field inclusion into the stage. -/
local instance relativeClassUpperStageAlgebra : Algebra (IntermediateField.fixedField V.toSubgroup) F :=
  (IntermediateField.inclusion hF.out).toAlgebra
/-- The relative upper module uses the original inclusion. -/
local instance relativeClassUpperStageModule : Module (IntermediateField.fixedField V.toSubgroup) F :=
  Algebra.toModule
/-- The relative upper scalar action uses the original inclusion. -/
local instance relativeClassUpperStageSMul : SMul (IntermediateField.fixedField V.toSubgroup) F :=
  Algebra.toSMul
/-- The relative upper multiplicative action uses the original module. -/
local instance relativeClassUpperStageMulAction : MulAction (IntermediateField.fixedField V.toSubgroup) F :=
  (relativeClassUpperStageModule Ω a V F).toDistribMulAction.toMulAction
/-- The upper fixed-field inclusion preserves the original rational tower. -/
local instance relativeClassUpperStageTower : IsScalarTower ℚ (IntermediateField.fixedField V.toSubgroup) F :=
  .of_algebraMap_eq' rfl

variable [hUF : Fact (IntermediateField.fixedField U.toSubgroup ≤ F.toIntermediateField)]

/-- The original lower fixed-field inclusion into the stage. -/
local instance relativeClassLowerStageAlgebra : Algebra (IntermediateField.fixedField U.toSubgroup) F :=
  (IntermediateField.inclusion hUF.out).toAlgebra
/-- The relative lower module uses the original inclusion. -/
local instance relativeClassLowerStageModule : Module (IntermediateField.fixedField U.toSubgroup) F :=
  Algebra.toModule
/-- The relative lower scalar action uses the original inclusion. -/
local instance relativeClassLowerStageSMul : SMul (IntermediateField.fixedField U.toSubgroup) F :=
  Algebra.toSMul
/-- The relative lower multiplicative action uses the original module. -/
local instance relativeClassLowerStageMulAction : MulAction (IntermediateField.fixedField U.toSubgroup) F :=
  (relativeClassLowerStageModule Ω a U F).toDistribMulAction.toMulAction
/-- The lower fixed-field inclusion preserves the original rational tower. -/
local instance relativeClassLowerStageTower : IsScalarTower ℚ (IntermediateField.fixedField U.toSubgroup) F :=
  .of_algebraMap_eq' rfl
/-- The finite arithmetic stage is Galois over the lower fixed field. -/
local instance relativeClassLowerStageGalois : IsGalois (IntermediateField.fixedField U.toSubgroup) F :=
  IsGalois.tower_top_of_isGalois ℚ _ F
/-- The genuine nested fixed-field inclusions form the finite stage tower. -/
local instance relativeClassStageTower : IsScalarTower (IntermediateField.fixedField U.toSubgroup)
    (IntermediateField.fixedField V.toSubgroup) F := .of_algebraMap_eq' rfl

/-- Literal class inclusion intertwines relative automorphisms at the actual finite stage. -/
theorem rationalArithmeticRelativeClassToStage_equivariant
    (σ : Gal(F / IntermediateField.fixedField U.toSubgroup))
    (c : rationalArithmeticOpenBaseClassQuotient Ω a ha V) :
    rationalArithmeticOpenBaseClassToStage Ω a ha V F
      ((rationalArithmeticRelativeClassRep Ω a ha U V).ρ
        (σ.restrictNormal (IntermediateField.fixedField V.toSubgroup)) c) =
    (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).ρ (σ.restrictScalars ℚ)
      (rationalArithmeticOpenBaseClassToStage Ω a ha V F c) := by
  let L := IntermediateField.fixedField U.toSubgroup
  let E := IntermediateField.fixedField V.toSubgroup
  exact Rep.hom_comm_apply (originalClassesModOutsideBaseChangeRepHom L E F
    (rationalArithmeticOpenBaseClassSupport Ω a ha V)
    (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (rationalArithmeticRelativeClassSupport_stable Ω a ha U V)
    (rationalArithmeticOpenStageSupport_stable Ω a ha U F)
    (rationalArithmeticOpenStageSupport_pullback Ω a ha V F)) σ c

omit hUF in
/-- Literal class base change intertwines the original open subgroup's relative restriction. -/
theorem rationalArithmeticOpenBaseClassToStage_equivariant
    (g : U) (c : rationalArithmeticOpenBaseClassQuotient Ω a ha V) :
    rationalArithmeticOpenBaseClassToStage Ω a ha V F
      ((rationalArithmeticRelativeClassRep Ω a ha U V).ρ
        (openGaloisSubgroupRelativeRestriction U V hVU.out g) c) =
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F).ρ g.val
      (rationalArithmeticOpenBaseClassToStage Ω a ha V F c) := by
  let L := IntermediateField.fixedField U.toSubgroup
  let E := IntermediateField.fixedField V.toSubgroup
  letI : Fact (L ≤ F.toIntermediateField) :=
    ⟨le_trans (IntermediateField.fixedField_le hVU.out) hF.out⟩
  letI : IsScalarTower L E F := .of_algebraMap_eq' rfl
  letI : IsScalarTower L F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower L E (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  have h := rationalArithmeticRelativeClassToStage_equivariant Ω a ha U V F
    ((openGaloisSubgroupFixedFieldEquiv U g).restrictNormal F) c
  have hr : ((openGaloisSubgroupFixedFieldEquiv U g).restrictNormal F).restrictNormal E =
      openGaloisSubgroupRelativeRestriction U V hVU.out g :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F
      (openGaloisSubgroupFixedFieldEquiv U g)).symm
  rw [hr, openGaloisSubgroup_restriction_commutes U F
    (le_trans (IntermediateField.fixedField_le hVU.out) hF.out) g] at h
  exact h

omit hUF hF in
/-- The genuine fixed-field class inclusion into the original colimit preserves the actual relative action. -/
theorem rationalArithmeticOpenBaseClassToColimit_equivariant
    [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
    (g : U) (c : rationalArithmeticOpenBaseClassQuotient Ω a ha V) :
    rationalArithmeticOpenBaseClassToColimit Ω a ha V
      ((rationalArithmeticRelativeClassRep Ω a ha U V).ρ
        (openGaloisSubgroupRelativeRestriction U V hVU.out g) c) =
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val
      (rationalArithmeticOpenBaseClassToColimit Ω a ha V c) := by
  let W := rationalArithmeticOpenClassBaseStage Ω a V
  letI : Fact (IntermediateField.fixedField V.toSubgroup ≤ W.toIntermediateField) :=
    ⟨rationalArithmeticOpenClassBaseStage_contains Ω a V⟩
  rw [← rationalArithmeticOpenBaseClassToColimit_stage Ω a ha V W,
    rationalArithmeticOpenBaseClassToStage_equivariant Ω a ha U V W g c]
  exact (Rep.hom_comm_apply (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) W) g.val
    (rationalArithmeticOpenBaseClassToStage Ω a ha V W c)).trans
      (congrArg ((arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val)
        (rationalArithmeticOpenBaseClassToColimit_stage Ω a ha V W c))

end
end Dubon2026
