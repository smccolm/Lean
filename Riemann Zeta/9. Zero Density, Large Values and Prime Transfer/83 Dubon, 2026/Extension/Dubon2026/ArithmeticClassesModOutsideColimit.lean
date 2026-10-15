import Dubon2026.ArithmeticClassesModOutsideStages
import Dubon2026.ArithmeticGlobalSourceColimits
import Dubon2026.CoefficientRepresentationColimitMap

/-! # Original arithmetic full classes modulo outside units

The actual finite quotient system carries the restricted arithmetic Galois
actions, and its coefficient colimit is a continuous discrete module. The
original S-place comparison induces an equivariant map into this colimit.
This is the original comparison map needed before class formation in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The actual finite full-class quotient with its original arithmetic Galois action. -/
abbrev arithmeticGlobalClassesModOutsideStageRep
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :=
  restrictedCoefficientRep (arithmeticClassesModOutsideStageRep K Ω a ha F)
    (AlgEquiv.restrictNormalHom F : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K))

/-- The original class quotient transition is equivariant for the same arithmetic Galois group. -/
def arithmeticGlobalClassesModOutsideStageTransition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) : arithmeticGlobalClassesModOutsideStageRep K Ω a ha E ⟶
      arithmeticGlobalClassesModOutsideStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) := .of_algebraMap_eq' rfl
  let φ := arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF
  refine Rep.ofHom { toLinearMap := φ.hom.toLinearMap, isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  exact (congrArg (fun σ : Gal(E/K) => φ.hom ((arithmeticClassesModOutsideStageRep K Ω a ha E).ρ σ x))
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g)).trans
      (Rep.hom_comm_apply φ (AlgEquiv.restrictNormalHom F g) x)

/-- The original finite source comparison retains its original arithmetic action. -/
def arithmeticGlobalSourceClassStageComparison
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    arithmeticGlobalSPlaceClassStageRep K Ω a ha F ⟶ arithmeticGlobalClassesModOutsideStageRep K Ω a ha F :=
  Rep.ofHom {
    toLinearMap := (arithmeticSourceClassStageComparison K Ω a ha F).hom.toLinearMap
    isIntertwining' := fun g => LinearMap.ext (fun x =>
      Rep.hom_comm_apply (arithmeticSourceClassStageComparison K Ω a ha F)
        (AlgEquiv.restrictNormalHom F g) x) }

private theorem comparison_natural
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F hEF ≫
      arithmeticGlobalSourceClassStageComparison K Ω a ha F =
        arithmeticGlobalSourceClassStageComparison K Ω a ha E ≫
          arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (arithmeticSourceClassStageComparison_natural K Ω a ha E F hEF x).symm

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual arithmetic full-class coefficient colimit modulo original outside units. -/
abbrev arithmeticClassesModOutsideColimitRep :=
  coefficientRepresentationColimit (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha)

/-- The genuine original arithmetic action on the discrete full-class quotient colimit is continuous. -/
theorem arithmeticClassesModOutsideColimitAction_continuous
    [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
    [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticClassesModOutsideColimitRep K Ω a ha =>
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ z.1 z.2) := by
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  apply coefficientRepresentationColimit_continuous
  intro F
  exact restrictedCoefficientAction_continuous (arithmeticClassesModOutsideStageRep K Ω a ha F) _
    (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) continuous_of_discreteTopology

/-- The literal original source comparison on the arithmetic coefficient colimits. -/
def arithmeticSourceClassColimitComparison :
    arithmeticSPlaceClassColimitRep K Ω a ha ⟶ arithmeticClassesModOutsideColimitRep K Ω a ha :=
  coefficientRepresentationColimitMap _ _ _ _
    (arithmeticGlobalSourceClassStageComparison K Ω a ha) (comparison_natural K Ω a ha)

/-- Each original source-class representative maps by the same literal finite-stage comparison. -/
theorem arithmeticSourceClassColimitComparison_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceClassFiniteStageRep K Ω a ha F) :
    (arithmeticSourceClassColimitComparison K Ω a ha).hom
      ((coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) F).hom x) =
        (coefficientRepresentationColimitOf _ (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
          ((arithmeticSourceClassStageComparison K Ω a ha F).hom x) :=
  coefficientRepresentationColimitMap_of _ _ _ _
    (arithmeticGlobalSourceClassStageComparison K Ω a ha) (comparison_natural K Ω a ha) F x

end
end Dubon2026
