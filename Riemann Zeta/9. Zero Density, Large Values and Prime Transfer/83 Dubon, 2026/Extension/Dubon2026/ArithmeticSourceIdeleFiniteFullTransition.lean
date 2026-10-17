import Dubon2026.OriginalSPlaceFullClassTowerImage
import Dubon2026.ArithmeticClassStageCocycleTransition

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original rational inclusion of the arithmetic union. -/
local instance sourceFiniteFullTransitionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual rational structure on each arithmetic stage. -/
local instance sourceFiniteFullTransitionStageAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Retain the same structure on its underlying intermediate field. -/
local instance sourceFiniteFullTransitionIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : IntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- The actual finite arithmetic stage is a number field. -/
local instance sourceFiniteFullTransitionNumberField
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) : NumberField E :=
  NumberField.of_module_finite ℚ E

/-- The specified source cocycle's actual full-idele H2 image. -/
def arithmeticSourceIdeleFiniteFullH2
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)) :
    groupCohomology (originalFullIdeleRep ℚ E) 2 :=
  (groupCohomology.functor ℤ Gal(E/ℚ) 2).map
    (originalSPlaceFullIdeleInclusion ℚ E (arithmeticSUnitFiniteStageSupport ℚ Ω a ha E)
      (originalExceptionalIntegerSupport_galoisStable E ℚ a ha)) (groupCohomology.H2π _ d)

/-- Transport this same full-idele representative to the common arithmetic
comparison field by the original vertical base-change map. -/
def arithmeticSourceIdeleFiniteFullH2Transition
    (E M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEM : E ≤ M)
    (d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)) :
    groupCohomology (originalFullIdeleRep ℚ M) 2 := by
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  exact originalFullIdeleBaseChangeH2 ℚ ℚ E M (arithmeticSourceIdeleFiniteFullH2 Ω a ha E d)

/-- The exact finite class cocycle used in the scalar comparison is the
outside-unit quotient of this specified full-idele class at the common field.
Thus the canonical total applies to an actual constructed idele input. -/
theorem arithmeticSourceIdeleFiniteFullH2Transition_class
    (E M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEM : E ≤ M)
    (d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E)) :
    groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E M hEM
      (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/ℚ))
        (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
          arithmeticSourceClassStageComparison ℚ Ω a ha E) d)) =
    (groupCohomology.functor ℤ Gal(M/ℚ) 2).map
      (originalIdeleClassesModOutsideRepHom ℚ M (arithmeticSUnitFiniteStageSupport ℚ Ω a ha M)
        (originalExceptionalIntegerSupport_galoisStable M ℚ a ha))
      ((groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
        (arithmeticSourceIdeleFiniteFullH2Transition Ω a ha E M hEM d)) := by
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  have h := originalSPlaceFullIdele_H2_class_tower_comparison ℚ E M
    (arithmeticSUnitFiniteStageSupport ℚ Ω a ha E) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha M)
    (originalExceptionalIntegerSupport_galoisStable E ℚ a ha)
    (originalExceptionalIntegerSupport_galoisStable M ℚ a ha)
    (arithmeticSPlaceFiniteStage_support ℚ Ω a ha E M hEM) (groupCohomology.H2π _ d)
  change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
    (groupCohomology.map _ _ 2 (groupCohomology.H2π _ d))) = _ at h
  simp only [groupCohomology.H2π_comp_map_apply] at h
  exact h

end
end Dubon2026
