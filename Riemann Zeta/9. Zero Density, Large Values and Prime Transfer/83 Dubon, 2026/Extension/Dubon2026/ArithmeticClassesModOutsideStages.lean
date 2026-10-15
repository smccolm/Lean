import Dubon2026.OriginalClassesModOutsideBaseChange
import Dubon2026.ArithmeticGlobalSourceStages

/-! # Actual finite-stage system of full classes modulo outside units

These are the original full idele classes at the same finite Galois fields
and exceptional support as the source coefficient sequence. The tower laws
are inherited from literal full-idele base change. This is the target system
for the remaining arithmetic class comparison in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The original full-class quotient at the actual finite arithmetic field and fixed support. -/
abbrev arithmeticClassesModOutsideStageRep
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  letI : NumberField E := NumberField.of_module_finite K E
  originalIdeleClassesModOutsideRep K E (arithmeticSUnitFiniteStageSupport K Ω a ha E)
    (originalExceptionalIntegerSupport_galoisStable E K a ha)

/-- Original full-class base change modulo outside units at the same finite arithmetic stages. -/
def arithmeticClassesModOutsideFiniteTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    restrictedCoefficientRep (arithmeticClassesModOutsideStageRep K Ω a ha E)
      (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) ⟶
        arithmeticClassesModOutsideStageRep K Ω a ha F := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  exact originalClassesModOutsideBaseChangeRepHom K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)

/-- The actual integer-linear transition of the original full-class quotients. -/
def arithmeticClassesModOutsideTransitionMap
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticClassesModOutsideStageRep K Ω a ha E →ₗ[ℤ]
      arithmeticClassesModOutsideStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  exact (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF).hom.toLinearMap

/-- The original full-class quotient transition over the same actual field is the identity. -/
theorem arithmeticClassesModOutsideTransitionMap_self
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticClassesModOutsideStageRep K Ω a ha E) :
    arithmeticClassesModOutsideTransitionMap K Ω a ha E E le_rfl x = x := by
  letI : NumberField E := NumberField.of_module_finite K E
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply congrArg Submodule.Quotient.mk
    apply Additive.toMul.injective
    apply originalIdeleClassBaseChangeMap_injective E E
    exact originalIdeleClassBaseChangeMap_tower E E E x.toMul

/-- The original full-class quotient transitions compose along actual finite arithmetic inclusions. -/
theorem arithmeticClassesModOutsideTransitionMap_comp
    (E F P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFP : F ≤ P) (x : arithmeticClassesModOutsideStageRep K Ω a ha E) :
    arithmeticClassesModOutsideTransitionMap K Ω a ha F P hFP
      (arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF x) =
        arithmeticClassesModOutsideTransitionMap K Ω a ha E P (hEF.trans hFP) x := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : NumberField P := NumberField.of_module_finite K P
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Algebra F P := (IntermediateField.inclusion hFP).toAlgebra
  letI : Algebra E P := (IntermediateField.inclusion (hEF.trans hFP)).toAlgebra
  haveI : IsScalarTower E F P := .of_algebraMap_eq' rfl
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply congrArg Submodule.Quotient.mk
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_tower E F P x.toMul)

/-- The actual full-class quotients at fixed support form a genuine directed system. -/
instance arithmeticClassesModOutsideDirectedSystem :
    DirectedSystem (fun E => arithmeticClassesModOutsideStageRep K Ω a ha E)
      (fun E F h => arithmeticClassesModOutsideTransitionMap K Ω a ha E F h) where
  map_self := fun {E} x => arithmeticClassesModOutsideTransitionMap_self K Ω a ha E x
  map_map := fun {P F E} hEF hFP x =>
    arithmeticClassesModOutsideTransitionMap_comp K Ω a ha E F P hEF hFP x

/-- The original source-class comparison at the same finite arithmetic stage. -/
def arithmeticSourceClassStageComparison
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    ArithmeticSPlaceClassFiniteStageRep K Ω a ha E ⟶ arithmeticClassesModOutsideStageRep K Ω a ha E := by
  letI : NumberField E := NumberField.of_module_finite K E
  exact originalSPlaceClassComparison K E _ _

/-- The original finite arithmetic comparison is injective without a principalization assumption. -/
theorem arithmeticSourceClassStageComparison_injective
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Function.Injective (arithmeticSourceClassStageComparison K Ω a ha E).hom := by
  letI : NumberField E := NumberField.of_module_finite K E
  exact originalSPlaceClassComparison_injective K E _ _

/-- The literal source comparison commutes with the actual arithmetic stage transitions. -/
theorem arithmeticSourceClassStageComparison_natural
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E) :
    arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF
      ((arithmeticSourceClassStageComparison K Ω a ha E).hom x) =
        (arithmeticSourceClassStageComparison K Ω a ha F).hom
          (arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF x) := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  exact originalSPlaceClassComparison_baseChange K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF) x

end
end Dubon2026
