import Dubon2026.OpenSubgroupFixedFieldRestriction
import Dubon2026.OriginalClassQuotientBaseInvariants
import Dubon2026.ArithmeticClassesModOutsideH1
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Original finite class invariants of an actual open arithmetic subgroup

Finite class descent is reused over the subgroup's genuine fixed field.
The original exceptional support and absolute unramifiedness are derived,
and the literal restriction comparison identifies the acting subgroup.
This supplies the finite coefficient step for the open-subgroup invariant
identity required by DUB-17's arithmetic class-formation route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The actual arithmetic union retains its original rational inclusion. -/
local instance openClassStageUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'
/-- The original arithmetic union is Galois over the rational field. -/
local instance openClassStageUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))

/-- The original fixed field carries its literal rational inclusion. -/
local instance openClassStageFixedAlgebra : Algebra ℚ (IntermediateField.fixedField H.toSubgroup) :=
  (IntermediateField.fixedField H.toSubgroup).algebra'
/-- Rational scalars on the fixed field use its original field algebra. -/
local instance openClassStageFixedRatSMul : SMul ℚ (IntermediateField.fixedField H.toSubgroup) :=
  Algebra.toSMul
/-- Openness makes the actual fixed field finite over the rationals. -/
local instance openClassStageFixedFinite : FiniteDimensional ℚ (IntermediateField.fixedField H.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite H
/-- The original open-subgroup fixed field is a number field. -/
local instance openClassStageFixedNumberField : NumberField (IntermediateField.fixedField H.toSubgroup) :=
  NumberField.of_module_finite ℚ _

/-- The original exceptional integer specifies the actual fixed-field support. -/
abbrev rationalArithmeticOpenBaseClassSupport :=
  originalExceptionalIntegerSupport (IntermediateField.fixedField H.toSubgroup)
    (algebraMap (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H.toSubgroup)) a)
    (originalIntegerMap_ne_zero (L := IntermediateField.fixedField H.toSubgroup) a ha)

/-- The genuine fixed-field classes modulo units outside the original support. -/
abbrev rationalArithmeticOpenBaseClassQuotient :=
  originalIdeleClassesModOutsideRep (IntermediateField.fixedField H.toSubgroup)
    (IntermediateField.fixedField H.toSubgroup) (rationalArithmeticOpenBaseClassSupport Ω a ha H)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  [hF : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField)]

/-- The actual stage retains the original rational field structure. -/
local instance openClassStageAlgebra : Algebra ℚ F := F.algebra'
/-- Rational scalars on the stage use its original field algebra. -/
local instance openClassStageRatSMul : SMul ℚ F := Algebra.toSMul
/-- The actual finite arithmetic stage is a number field. -/
local instance openClassStageNumberField : NumberField F := NumberField.of_module_finite ℚ F
/-- Containment supplies the literal fixed-field inclusion into the stage. -/
local instance openClassStageRelativeAlgebra : Algebra (IntermediateField.fixedField H.toSubgroup) F :=
  (IntermediateField.inclusion hF.out).toAlgebra
/-- The relative module structure is the one induced by the original field inclusion. -/
local instance openClassStageRelativeModule : Module (IntermediateField.fixedField H.toSubgroup) F :=
  Algebra.toModule
/-- Relative scalar multiplication uses the same original field inclusion. -/
local instance openClassStageRelativeSMul : SMul (IntermediateField.fixedField H.toSubgroup) F :=
  Algebra.toSMul
/-- The relative field action uses the original scalar multiplication. -/
local instance openClassStageRelativeMulAction : MulAction (IntermediateField.fixedField H.toSubgroup) F :=
  (openClassStageRelativeModule Ω a H F).toDistribMulAction.toMulAction
/-- The original field inclusions form the rational scalar tower. -/
local instance openClassStageRelativeTower : IsScalarTower ℚ (IntermediateField.fixedField H.toSubgroup) F :=
  .of_algebraMap_eq' rfl
/-- The original finite stage is Galois over the actual fixed field. -/
local instance openClassStageRelativeGalois : IsGalois (IntermediateField.fixedField H.toSubgroup) F :=
  IsGalois.tower_top_of_isGalois ℚ _ F

include hF in
/-- The arithmetic stage support is stable under its actual fixed-field automorphisms. -/
theorem rationalArithmeticOpenStageSupport_stable
    (σ : Gal(F/IntermediateField.fixedField H.toSubgroup)) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ arithmeticSUnitFiniteStageSupport ℚ Ω a ha F ↔
      numberFieldGaloisPlaceEquiv (IntermediateField.fixedField H.toSubgroup) F σ v ∈
        arithmeticSUnitFiniteStageSupport ℚ Ω a ha F :=
  originalExceptionalIntegerSupport_galoisStable F ℚ a ha (σ.restrictScalars ℚ) v

include hF in
/-- The original exceptional supports agree under the literal fixed-field prime restriction. -/
theorem rationalArithmeticOpenStageSupport_pullback (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ arithmeticSUnitFiniteStageSupport ℚ Ω a ha F ↔
      originalFinitePrimeBelow (IntermediateField.fixedField H.toSubgroup) F w ∈
        rationalArithmeticOpenBaseClassSupport Ω a ha H := by
  change w ∈ originalExceptionalIntegerSupport F _ _ ↔
    originalFinitePrimeBelow (IntermediateField.fixedField H.toSubgroup) F w ∈ originalExceptionalIntegerSupport _ _ _
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  change algebraMap (𝓞 ℚ) (𝓞 F) a ∈ w.asIdeal ↔
    algebraMap (𝓞 (IntermediateField.fixedField H.toSubgroup)) (𝓞 F)
      (algebraMap (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H.toSubgroup)) a) ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 (IntermediateField.fixedField H.toSubgroup)) (𝓞 F)]

/-- Literal fixed-field class inclusion into the original finite arithmetic coefficient. -/
def rationalArithmeticOpenBaseClassToStage :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H →ₗ[ℤ]
      arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F :=
  (originalClassesModOutsideBaseChangeRepHom
    (IntermediateField.fixedField H.toSubgroup) (IntermediateField.fixedField H.toSubgroup) F
    (rationalArithmeticOpenBaseClassSupport Ω a ha H) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])
    (rationalArithmeticOpenStageSupport_stable Ω a ha H F)
    (rationalArithmeticOpenStageSupport_pullback Ω a ha H F)).hom.toLinearMap

/-- The same literal class inclusion, viewed as an invariant under fixed-field automorphisms. -/
def rationalArithmeticOpenBaseClassToRelativeInvariants :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H →ₗ[ℤ]
      (originalIdeleClassesModOutsideRep (IntermediateField.fixedField H.toSubgroup) F
        (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
        (rationalArithmeticOpenStageSupport_stable Ω a ha H F)).ρ.invariants :=
  originalClassesModOutsideBaseInvariant (IntermediateField.fixedField H.toSubgroup) F
    (rationalArithmeticOpenBaseClassSupport Ω a ha H) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])
    (rationalArithmeticOpenStageSupport_stable Ω a ha H F)
    (rationalArithmeticOpenStageSupport_pullback Ω a ha H F)

/-- The original finite invariant-descent theorem applies with all arithmetic hypotheses discharged. -/
theorem rationalArithmeticOpenBaseClassToRelativeInvariants_bijective :
    Function.Bijective (rationalArithmeticOpenBaseClassToRelativeInvariants Ω a ha H F) :=
  originalClassesModOutsideBaseInvariant_bijective (IntermediateField.fixedField H.toSubgroup) F
    (rationalArithmeticOpenBaseClassSupport Ω a ha H) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (fun σ v => by
      have he : σ = 1 := Subsingleton.elim _ _
      rw [he, numberFieldGaloisPlaceEquiv_one])
    (rationalArithmeticOpenStageSupport_stable Ω a ha H F)
    (rationalArithmeticOpenStageSupport_pullback Ω a ha H F)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

/-- Literal fixed-field classes at the finite stage are fixed by the original open subgroup. -/
theorem rationalArithmeticOpenBaseClassToStage_fixed
    (c : rationalArithmeticOpenBaseClassQuotient Ω a ha H) (g : H) :
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F).ρ (g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
      (rationalArithmeticOpenBaseClassToStage Ω a ha H F c) =
        rationalArithmeticOpenBaseClassToStage Ω a ha H F c := by
  letI : IsScalarTower (IntermediateField.fixedField H.toSubgroup) F
      (originalUnramifiedGaloisUnion (Ω := Ω) a) := .of_algebraMap_eq' rfl
  have hi := (rationalArithmeticOpenBaseClassToRelativeInvariants Ω a ha H F c).property
    ((openGaloisSubgroupFixedFieldEquiv H g).restrictNormal F)
  change (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).ρ
    (((openGaloisSubgroupFixedFieldEquiv H g).restrictNormal F).restrictScalars ℚ)
    (rationalArithmeticOpenBaseClassToStage Ω a ha H F c) =
      rationalArithmeticOpenBaseClassToStage Ω a ha H F c at hi
  rw [openGaloisSubgroup_restriction_commutes H F hF.out g] at hi
  exact hi

/-- The actual fixed-field class map into the finite stage restricted to the original open-subgroup invariants. -/
def rationalArithmeticOpenBaseClassToStageInvariants :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H →ₗ[ℤ]
      (Rep.res H.toSubgroup.subtype (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F)).ρ.invariants :=
  (rationalArithmeticOpenBaseClassToStage Ω a ha H F).codRestrict _
    (rationalArithmeticOpenBaseClassToStage_fixed Ω a ha H F)

/-- Every original open-subgroup invariant finite-stage class has a unique actual fixed-field class preimage. -/
theorem rationalArithmeticOpenBaseClassToStageInvariants_bijective :
    Function.Bijective (rationalArithmeticOpenBaseClassToStageInvariants Ω a ha H F) := by
  have hj := rationalArithmeticOpenBaseClassToRelativeInvariants_bijective Ω a ha H F
  constructor
  · intro c d h
    apply hj.1
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact he
  · intro x
    have hx : ∀ σ : Gal(F/IntermediateField.fixedField H.toSubgroup),
        (originalIdeleClassesModOutsideRep (IntermediateField.fixedField H.toSubgroup) F
          (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
          (rationalArithmeticOpenStageSupport_stable Ω a ha H F)).ρ σ x.val = x.val := by
      intro σ
      have hlift := openGaloisSubgroup_restriction_surjective H F hF.out σ
      obtain ⟨g, hg⟩ := hlift
      have he := x.property g
      change (arithmeticClassesModOutsideStageRep ℚ Ω a ha F).ρ
        (AlgEquiv.restrictNormalHom F (g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))) x.val = x.val at he
      rw [hg] at he
      exact he
    obtain ⟨c, hc⟩ := hj.2 ⟨x.val, hx⟩
    have he := congrArg Subtype.val hc
    exact ⟨c, Subtype.ext he⟩

end
end Dubon2026
