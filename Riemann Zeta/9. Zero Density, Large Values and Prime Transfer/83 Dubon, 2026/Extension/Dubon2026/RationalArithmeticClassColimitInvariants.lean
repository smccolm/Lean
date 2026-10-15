import Dubon2026.RationalArithmeticClassQuotientInvariants
import Dubon2026.ArithmeticClassColimitFixedStages

/-! # The original rational class quotient equals the arithmetic colimit invariants

Literal base-field class inclusions agree at every original finite stage.
Faithful stage maps and finite invariant descent therefore identify the
actual global invariant coefficient. This removes the rational invariant
coefficient premise in the arithmetic class formation serving DUB-17.
Compatible invariant maps, all open subgroups and Ext duality remain open.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (Ω : Type) [Field Ω] [Algebra ℚ Ω]

/-- The original arithmetic union carries its literal rational inclusion. -/
local instance classColimitInvariantUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- The actual base quotient map to an original arithmetic finite stage. -/
def rationalArithmeticBaseClassToStage
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    rationalArithmeticBaseClassQuotient a ha →ₗ[ℤ] arithmeticClassesModOutsideStageRep ℚ Ω a ha F :=
  (Submodule.subtype _).comp (rationalArithmeticClassQuotientInvariantEquiv a ha Ω F).toLinearMap

/-- The actual base quotient maps commute with the literal arithmetic field transitions. -/
theorem rationalArithmeticBaseClassToStage_transition
    (E F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (c : rationalArithmeticBaseClassQuotient a ha) :
    arithmeticClassesModOutsideTransitionMap ℚ Ω a ha E F hEF
      (rationalArithmeticBaseClassToStage a ha Ω E c) =
        rationalArithmeticBaseClassToStage a ha Ω F c := by
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra ℚ F := F.algebra'
  letI : SMul ℚ E := Algebra.toSMul
  letI : SMul ℚ F := Algebra.toSMul
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := Algebra.toSMul
  haveI : IsScalarTower ℚ E F := .of_algebraMap_eq' rfl
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (Additive.ofMul
      (originalIdeleClassBaseChangeMap E F (originalIdeleClassBaseChangeMap ℚ E c.toMul))) =
      Submodule.Quotient.mk (Additive.ofMul (originalIdeleClassBaseChangeMap ℚ F c.toMul))
    exact congrArg (fun z => Submodule.Quotient.mk (Additive.ofMul z))
      (originalIdeleClassBaseChangeMap_tower ℚ E F c.toMul)

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual base quotient embeds into the original arithmetic class colimit via its bottom finite stage. -/
def rationalArithmeticBaseClassToColimit :
    rationalArithmeticBaseClassQuotient a ha →ₗ[ℤ] arithmeticClassesModOutsideColimitRep ℚ Ω a ha :=
  (coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) ⊥).hom.toLinearMap.comp
      (rationalArithmeticBaseClassToStage a ha Ω ⊥)

/-- Every original finite-stage representative of an actual base quotient class gives the same original colimit coefficient. -/
theorem rationalArithmeticBaseClassToColimit_stage
    (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : rationalArithmeticBaseClassQuotient a ha) :
    (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F).hom
      (rationalArithmeticBaseClassToStage a ha Ω F c) =
        rationalArithmeticBaseClassToColimit a ha Ω c := by
  rw [← rationalArithmeticBaseClassToStage_transition a ha Ω ⊥ F bot_le c]
  exact Module.DirectLimit.of_f
    (R := ℤ) (G := fun E => arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha E)
    (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha E F h).hom.toLinearMap)
    (hij := bot_le) (x := rationalArithmeticBaseClassToStage a ha Ω ⊥ c)

/-- Actual base quotient classes are fixed by the original arithmetic Galois action. -/
theorem rationalArithmeticBaseClassToColimit_fixed
    (c : rationalArithmeticBaseClassQuotient a ha)
    (g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ)) :
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g
      (rationalArithmeticBaseClassToColimit a ha Ω c) =
        rationalArithmeticBaseClassToColimit a ha Ω c := by
  apply (arithmeticClassesModOutsideColimitOf_fixed_iff ℚ Ω a ha ⊥
    (rationalArithmeticBaseClassToStage a ha Ω ⊥ c)).mpr
    (rationalArithmeticClassQuotientInvariantEquiv a ha Ω ⊥ c).property

/-- The actual rational base quotient map into the arithmetic colimit is injective. -/
theorem rationalArithmeticBaseClassToColimit_injective :
    Function.Injective (rationalArithmeticBaseClassToColimit a ha Ω) := by
  intro c d h
  apply (rationalArithmeticClassQuotientInvariantEquiv a ha Ω ⊥).injective
  apply Subtype.ext
  exact arithmeticClassesModOutsideColimitOf_injective ℚ Ω a ha ⊥ h

/-- The actual base quotient map, with codomain restricted to the literal global invariants. -/
def rationalArithmeticBaseClassToColimitInvariants :
    rationalArithmeticBaseClassQuotient a ha →ₗ[ℤ]
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ.invariants :=
  (rationalArithmeticBaseClassToColimit a ha Ω).codRestrict _
    (rationalArithmeticBaseClassToColimit_fixed a ha Ω)

/-- Every original arithmetic invariant class coefficient has a unique genuine rational base quotient preimage. -/
theorem rationalArithmeticBaseClassToColimitInvariants_bijective :
    Function.Bijective (rationalArithmeticBaseClassToColimitInvariants a ha Ω) := by
  constructor
  · intro c d h
    exact rationalArithmeticBaseClassToColimit_injective a ha Ω (congrArg Subtype.val h)
  · intro x
    obtain ⟨F, y, hy⟩ := arithmeticClassesModOutsideColimit_fixed_exists_stage ℚ Ω a ha
      x.val x.property
    let c := (rationalArithmeticClassQuotientInvariantEquiv a ha Ω F).symm y
    refine ⟨c, Subtype.ext ?_⟩
    change rationalArithmeticBaseClassToColimit a ha Ω c = x.val
    rw [← rationalArithmeticBaseClassToColimit_stage a ha Ω F c]
    have hc : rationalArithmeticBaseClassToStage a ha Ω F c = y.val :=
      congrArg Subtype.val ((rationalArithmeticClassQuotientInvariantEquiv a ha Ω F).apply_symm_apply y)
    rw [hc]
    exact hy

/-- The genuine rational base quotient equals the literal original arithmetic class-colimit invariant coefficient. -/
def rationalArithmeticClassColimitInvariantEquiv :
    rationalArithmeticBaseClassQuotient a ha ≃ₗ[ℤ]
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ.invariants :=
  LinearEquiv.ofBijective (rationalArithmeticBaseClassToColimitInvariants a ha Ω)
    (rationalArithmeticBaseClassToColimitInvariants_bijective a ha Ω)

end
end Dubon2026
