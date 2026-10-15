import Dubon2026.ArithmeticSPlaceDirectedSystems
import Dubon2026.ArithmeticSUnitCoefficientColimit

/-! # Actual arithmetic Galois actions on the original finite source stages

Each original finite action is restricted along the literal global Galois
restriction. The proved normal-restriction tower identity makes the original
S-unit, source idele and source class transitions equivariant for the same
arithmetic Galois group. These supply the original actions for their colimits.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

private def restrictStageHom
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (A : Rep ℤ Gal(E/K)) (B : Rep ℤ Gal(F/K)) :
    (letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra;
      restrictedCoefficientRep A (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) ⟶ B) →
      (restrictedCoefficientRep A (AlgEquiv.restrictNormalHom E :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(E/K)) ⟶
      restrictedCoefficientRep B (AlgEquiv.restrictNormalHom F :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) := .of_algebraMap_eq' rfl
  intro φ
  refine Rep.ofHom { toLinearMap := φ.hom.toLinearMap, isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  exact (congrArg (fun σ : Gal(E/K) => φ.hom (A.ρ σ x))
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g)).trans
      (Rep.hom_comm_apply φ (AlgEquiv.restrictNormalHom F g) x)

/-- The same original finite S-unit coefficient with its restricted actual global Galois action. -/
abbrev arithmeticGlobalSUnitStageRep
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha F)
    (AlgEquiv.restrictNormalHom F : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))

/-- The same source S-place coefficient with its restricted actual global Galois action. -/
abbrev arithmeticGlobalSPlaceStageRep
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  restrictedCoefficientRep (ArithmeticSPlaceFiniteStageRep K Ω a ha F)
    (AlgEquiv.restrictNormalHom F : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))

/-- The same source class coefficient with its restricted actual global Galois action. -/
abbrev arithmeticGlobalSPlaceClassStageRep
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  restrictedCoefficientRep (ArithmeticSPlaceClassFiniteStageRep K Ω a ha F)
    (AlgEquiv.restrictNormalHom F : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))

/-- The actual S-unit transition is equivariant for the original arithmetic Galois action. -/
def arithmeticGlobalSUnitStageTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticGlobalSUnitStageRep K Ω a ha E ⟶ arithmeticGlobalSUnitStageRep K Ω a ha F :=
  restrictStageHom K Ω a E F hEF _ _ (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF)

/-- The actual source idele transition is equivariant for the same arithmetic Galois action. -/
def arithmeticGlobalSPlaceStageTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticGlobalSPlaceStageRep K Ω a ha E ⟶ arithmeticGlobalSPlaceStageRep K Ω a ha F :=
  restrictStageHom K Ω a E F hEF _ _ (arithmeticSPlaceFiniteTransition K Ω a ha E F hEF)

/-- The actual source class transition is equivariant for the same arithmetic Galois action. -/
def arithmeticGlobalSPlaceClassStageTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticGlobalSPlaceClassStageRep K Ω a ha E ⟶ arithmeticGlobalSPlaceClassStageRep K Ω a ha F :=
  restrictStageHom K Ω a E F hEF _ _ (arithmeticSPlaceClassFiniteTransition K Ω a ha E F hEF)

/-- Global restriction preserves the literal S-unit coefficient transition already used by the arithmetic colimit. -/
theorem arithmeticGlobalSUnitStageTransition_apply
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : arithmeticSUnitFiniteStageRep K Ω a ha E) :
    (arithmeticGlobalSUnitStageTransition K Ω a ha E F hEF).hom x =
      arithmeticSUnitCoefficientTransition K Ω a ha E F hEF x := rfl

/-- Global restriction preserves the literal source idele transition. -/
theorem arithmeticGlobalSPlaceStageTransition_apply
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : ArithmeticSPlaceFiniteStageRep K Ω a ha E) :
    (arithmeticGlobalSPlaceStageTransition K Ω a ha E F hEF).hom x =
      arithmeticSPlaceTransitionMap K Ω a ha E F hEF x := rfl

/-- Global restriction preserves the literal source class transition. -/
theorem arithmeticGlobalSPlaceClassStageTransition_apply
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) (x : ArithmeticSPlaceClassFiniteStageRep K Ω a ha E) :
    (arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F hEF).hom x =
      arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF x := rfl

end
end Dubon2026
