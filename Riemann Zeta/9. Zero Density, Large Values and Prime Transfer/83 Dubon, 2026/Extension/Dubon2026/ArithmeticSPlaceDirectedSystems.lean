import Dubon2026.ArithmeticSPlaceFiniteStages
import Dubon2026.OriginalSPlaceBaseChangeTower
import Mathlib.Algebra.Colimit.Module

/-! # Genuine finite arithmetic systems of source ideles and source classes

The source maps satisfy their directed-system laws by the original idele
tower theorem and literal quotient induction. No transition law is supplied
as a premise. These systems are the inputs to the fixed-support coefficient
colimits required in DUB-17's global-duality route.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The actual linear source idele transition at the same arithmetic finite stages. -/
def arithmeticSPlaceTransitionMap
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : ArithmeticSPlaceFiniteStageRep K Ω a ha E →ₗ[ℤ]
      ArithmeticSPlaceFiniteStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  exact (arithmeticSPlaceFiniteTransition K Ω a ha E F hEF).hom.toLinearMap

/-- The actual linear source class transition induced on the same original finite quotients. -/
def arithmeticSPlaceClassTransitionMap
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E →ₗ[ℤ]
      ArithmeticSPlaceClassFiniteStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  exact (arithmeticSPlaceClassFiniteTransition K Ω a ha E F hEF).hom.toLinearMap

/-- The same-field arithmetic source idele transition is the identity. -/
theorem arithmeticSPlaceTransitionMap_self
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceFiniteStageRep K Ω a ha E) :
    arithmeticSPlaceTransitionMap K Ω a ha E E le_rfl x = x := by
  letI : NumberField E := NumberField.of_module_finite K E
  exact originalSPlaceBaseChange_self E _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E E le_rfl) x

/-- The original arithmetic source idele transition maps compose along actual field inclusions. -/
theorem arithmeticSPlaceTransitionMap_comp
    (E F P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFP : F ≤ P) (x : ArithmeticSPlaceFiniteStageRep K Ω a ha E) :
    arithmeticSPlaceTransitionMap K Ω a ha F P hFP
      (arithmeticSPlaceTransitionMap K Ω a ha E F hEF x) =
        arithmeticSPlaceTransitionMap K Ω a ha E P (hEF.trans hFP) x := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : NumberField P := NumberField.of_module_finite K P
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Algebra F P := (IntermediateField.inclusion hFP).toAlgebra
  letI : Algebra E P := (IntermediateField.inclusion (hEF.trans hFP)).toAlgebra
  haveI : IsScalarTower E F P := .of_algebraMap_eq' rfl
  exact originalSPlaceBaseChange_tower E F P _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)
    (arithmeticSPlaceFiniteStage_support K Ω a ha F P hFP)
    (arithmeticSPlaceFiniteStage_support K Ω a ha E P (hEF.trans hFP)) x

/-- The original arithmetic source class transition is the identity at the same field. -/
theorem arithmeticSPlaceClassTransitionMap_self
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E) :
    arithmeticSPlaceClassTransitionMap K Ω a ha E E le_rfl x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    exact congrArg Submodule.Quotient.mk (arithmeticSPlaceTransitionMap_self K Ω a ha E y)

/-- The actual arithmetic source class maps compose on their original quotient representatives. -/
theorem arithmeticSPlaceClassTransitionMap_comp
    (E F P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (hFP : F ≤ P) (x : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E) :
    arithmeticSPlaceClassTransitionMap K Ω a ha F P hFP
      (arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF x) =
        arithmeticSPlaceClassTransitionMap K Ω a ha E P (hEF.trans hFP) x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    exact congrArg Submodule.Quotient.mk (arithmeticSPlaceTransitionMap_comp K Ω a ha E F P hEF hFP y)

/-- The original arithmetic source idele maps form a genuine directed system. -/
instance arithmeticSPlaceDirectedSystem :
    DirectedSystem (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
      (fun E F h => arithmeticSPlaceTransitionMap K Ω a ha E F h) where
  map_self := fun {E} x => arithmeticSPlaceTransitionMap_self K Ω a ha E x
  map_map := fun {P F E} hEF hFP x => arithmeticSPlaceTransitionMap_comp K Ω a ha E F P hEF hFP x

/-- The original arithmetic source class maps form the corresponding genuine directed system. -/
instance arithmeticSPlaceClassDirectedSystem :
    DirectedSystem (fun F => ArithmeticSPlaceClassFiniteStageRep K Ω a ha F)
      (fun E F h => arithmeticSPlaceClassTransitionMap K Ω a ha E F h) where
  map_self := fun {E} x => arithmeticSPlaceClassTransitionMap_self K Ω a ha E x
  map_map := fun {P F E} hEF hFP x => arithmeticSPlaceClassTransitionMap_comp K Ω a ha E F P hEF hFP x

end
end Dubon2026
