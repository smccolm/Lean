import Dubon2026.RationalArithmeticOpenClassStageInvariants
import Dubon2026.ArithmeticOpenClassColimitFixedStages

/-! # Genuine fixed-field classes are the original open-subgroup colimit invariants

Literal class base change commutes with the original finite-stage maps.
Faithful colimit inclusions and finite fixed-field descent therefore give
the required open-subgroup coefficient identity. This removes an input to
DUB-17's arithmetic P-class formation; normalized H2 invariant maps and
the subsequent Ext/localization comparison remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original union carries its literal rational field inclusion. -/
local instance openClassColimitUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'
/-- The original arithmetic union is Galois. -/
local instance openClassColimitUnionGalois : IsGalois ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))

/-- The actual fixed field carries its original rational algebra. -/
local instance openClassColimitFixedAlgebra : Algebra ℚ (IntermediateField.fixedField H.toSubgroup) :=
  (IntermediateField.fixedField H.toSubgroup).algebra'
/-- The actual open-subgroup fixed field is finite over the rationals. -/
local instance openClassColimitFixedFinite : FiniteDimensional ℚ (IntermediateField.fixedField H.toSubgroup) :=
  openGaloisSubgroup_fixedField_finite H
/-- The actual fixed field is a number field. -/
local instance openClassColimitFixedNumberField : NumberField (IntermediateField.fixedField H.toSubgroup) :=
  NumberField.of_module_finite ℚ _

/-- An original finite Galois stage containing the actual open-subgroup fixed field. -/
def rationalArithmeticOpenClassBaseStage :
    FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  Classical.choose (openGaloisSubgroup_exists_finite_stage H ⊥)

/-- The chosen original finite stage contains the genuine fixed field. -/
theorem rationalArithmeticOpenClassBaseStage_contains :
    IntermediateField.fixedField H.toSubgroup ≤ (rationalArithmeticOpenClassBaseStage Ω a H).toIntermediateField :=
  (Classical.choose_spec (openGaloisSubgroup_exists_finite_stage H ⊥)).2

/-- Literal fixed-field class inclusions commute with the actual arithmetic finite-stage transitions. -/
theorem rationalArithmeticOpenBaseClassToStage_transition
    (E F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [hE : Fact (IntermediateField.fixedField H.toSubgroup ≤ E.toIntermediateField)]
    [hF : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField)]
    (hEF : E ≤ F) (c : rationalArithmeticOpenBaseClassQuotient Ω a ha H) :
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha E F hEF).hom
      (rationalArithmeticOpenBaseClassToStage Ω a ha H E c) =
        rationalArithmeticOpenBaseClassToStage Ω a ha H F c := by
  let L := IntermediateField.fixedField H.toSubgroup
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : Algebra L E := (IntermediateField.inclusion hE.out).toAlgebra
  letI : Algebra L F := (IntermediateField.inclusion hF.out).toAlgebra
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module L E := Algebra.toModule
  letI : Module L F := Algebra.toModule
  letI : Module E F := Algebra.toModule
  letI : SMul L E := Algebra.toSMul
  letI : SMul L F := Algebra.toSMul
  letI : SMul E F := Algebra.toSMul
  letI : IsScalarTower L E F := .of_algebraMap_eq' rfl
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (Additive.ofMul
      (originalIdeleClassBaseChangeMap E F (originalIdeleClassBaseChangeMap L E c.toMul))) =
      Submodule.Quotient.mk (Additive.ofMul (originalIdeleClassBaseChangeMap L F c.toMul))
    exact congrArg (fun z => Submodule.Quotient.mk (Additive.ofMul z))
      (originalIdeleClassBaseChangeMap_tower L E F c.toMul)

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Actual fixed-field class coefficients have the same original colimit value along every finite-stage transition. -/
theorem rationalArithmeticOpenBaseClassToColimit_transition
    (E F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [Fact (IntermediateField.fixedField H.toSubgroup ≤ E.toIntermediateField)]
    [Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField)]
    (hEF : E ≤ F) (c : rationalArithmeticOpenBaseClassQuotient Ω a ha H) :
    (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F).hom
      (rationalArithmeticOpenBaseClassToStage Ω a ha H F c) =
    (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) E).hom
      (rationalArithmeticOpenBaseClassToStage Ω a ha H E c) := by
  rw [← rationalArithmeticOpenBaseClassToStage_transition Ω a ha H E F hEF c]
  exact Module.DirectLimit.of_f
    (R := ℤ) (G := fun D => arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha D)
    (f := fun D E h => (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha D E h).hom.toLinearMap)
    (hij := hEF) (x := rationalArithmeticOpenBaseClassToStage Ω a ha H E c)

/-- The genuine fixed-field class quotient maps to the original arithmetic colimit. -/
def rationalArithmeticOpenBaseClassToColimit :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H →ₗ[ℤ]
      arithmeticClassesModOutsideColimitRep ℚ Ω a ha := by
  let W := rationalArithmeticOpenClassBaseStage Ω a H
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ W.toIntermediateField) :=
    ⟨rationalArithmeticOpenClassBaseStage_contains Ω a H⟩
  exact (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) W).hom.toLinearMap.comp
      (rationalArithmeticOpenBaseClassToStage Ω a ha H W)

/-- Every original finite stage above the fixed field gives the same literal fixed-field class map to the colimit. -/
theorem rationalArithmeticOpenBaseClassToColimit_stage
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [hF : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField)]
    (c : rationalArithmeticOpenBaseClassQuotient Ω a ha H) :
    (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F).hom
      (rationalArithmeticOpenBaseClassToStage Ω a ha H F c) =
        rationalArithmeticOpenBaseClassToColimit Ω a ha H c := by
  let W := rationalArithmeticOpenClassBaseStage Ω a H
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ W.toIntermediateField) :=
    ⟨rationalArithmeticOpenClassBaseStage_contains Ω a H⟩
  let D := F ⊔ W
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ D.toIntermediateField) :=
    ⟨le_trans hF.out le_sup_left⟩
  have h₁ := rationalArithmeticOpenBaseClassToColimit_transition Ω a ha H F D le_sup_left c
  have h₂ := rationalArithmeticOpenBaseClassToColimit_transition Ω a ha H W D le_sup_right c
  exact h₁.symm.trans h₂

/-- The literal fixed-field classes in the original colimit are fixed by the actual open subgroup. -/
theorem rationalArithmeticOpenBaseClassToColimit_fixed
    (c : rationalArithmeticOpenBaseClassQuotient Ω a ha H) (g : H) :
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val
      (rationalArithmeticOpenBaseClassToColimit Ω a ha H c) =
        rationalArithmeticOpenBaseClassToColimit Ω a ha H c := by
  let W := rationalArithmeticOpenClassBaseStage Ω a H
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ W.toIntermediateField) :=
    ⟨rationalArithmeticOpenClassBaseStage_contains Ω a H⟩
  exact (arithmeticClassesModOutsideColimitOf_open_fixed_iff ℚ Ω a ha H W
    (rationalArithmeticOpenBaseClassToStage Ω a ha H W c)).mpr
      (rationalArithmeticOpenBaseClassToStage_fixed Ω a ha H W c) g

/-- The original fixed-field class map to the arithmetic colimit is injective. -/
theorem rationalArithmeticOpenBaseClassToColimit_injective :
    Function.Injective (rationalArithmeticOpenBaseClassToColimit Ω a ha H) := by
  let W := rationalArithmeticOpenClassBaseStage Ω a H
  letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ W.toIntermediateField) :=
    ⟨rationalArithmeticOpenClassBaseStage_contains Ω a H⟩
  intro c d h
  apply (rationalArithmeticOpenBaseClassToStageInvariants_bijective Ω a ha H W).1
  apply Subtype.ext
  exact arithmeticClassesModOutsideColimitOf_injective ℚ Ω a ha W h

/-- The literal original fixed-field class map with codomain the actual open-subgroup colimit invariants. -/
def rationalArithmeticOpenBaseClassToColimitInvariants :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H →ₗ[ℤ]
      (Rep.res H.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).ρ.invariants :=
  (rationalArithmeticOpenBaseClassToColimit Ω a ha H).codRestrict _
    (rationalArithmeticOpenBaseClassToColimit_fixed Ω a ha H)

/-- Every actual open-subgroup invariant arithmetic class coefficient has a unique genuine fixed-field class preimage. -/
theorem rationalArithmeticOpenBaseClassToColimitInvariants_bijective :
    Function.Bijective (rationalArithmeticOpenBaseClassToColimitInvariants Ω a ha H) := by
  constructor
  · intro c d h
    exact rationalArithmeticOpenBaseClassToColimit_injective Ω a ha H (congrArg Subtype.val h)
  · intro x
    let W := rationalArithmeticOpenClassBaseStage Ω a H
    have hstage := arithmeticClassesModOutsideColimit_open_fixed_exists_stage_above ℚ Ω a ha H W
      x.val x.property
    obtain ⟨F, hWF, y, hy⟩ := hstage
    letI : Fact (IntermediateField.fixedField H.toSubgroup ≤ F.toIntermediateField) :=
      ⟨le_trans (rationalArithmeticOpenClassBaseStage_contains Ω a H) hWF⟩
    have hpre := (rationalArithmeticOpenBaseClassToStageInvariants_bijective Ω a ha H F).2 y
    obtain ⟨c, hc⟩ := hpre
    refine ⟨c, Subtype.ext ?_⟩
    change rationalArithmeticOpenBaseClassToColimit Ω a ha H c = x.val
    rw [← rationalArithmeticOpenBaseClassToColimit_stage Ω a ha H F c]
    have he := congrArg Subtype.val hc
    change rationalArithmeticOpenBaseClassToStage Ω a ha H F c = y.val at he
    rw [he]
    exact hy

/-- Genuine classes of the actual fixed field equal the literal open-subgroup invariants in the original arithmetic class colimit. -/
def rationalArithmeticOpenClassColimitInvariantEquiv :
    rationalArithmeticOpenBaseClassQuotient Ω a ha H ≃ₗ[ℤ]
      (Rep.res H.toSubgroup.subtype (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)).ρ.invariants :=
  LinearEquiv.ofBijective (rationalArithmeticOpenBaseClassToColimitInvariants Ω a ha H)
    (rationalArithmeticOpenBaseClassToColimitInvariants_bijective Ω a ha H)

end
end Dubon2026
