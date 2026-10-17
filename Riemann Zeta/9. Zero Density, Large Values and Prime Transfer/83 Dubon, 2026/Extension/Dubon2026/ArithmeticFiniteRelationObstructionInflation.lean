import Dubon2026.OriginalRestrictedRelationObstruction
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # The finite class relation obstruction in the actual arithmetic colimit

Instantiate original connecting naturality at the literal finite Galois
restriction and class-colimit inclusion. This is the next edge from DUB-17's
descended relation representative to its global continuous cup comparison.
No inflation or comparison certificate is supplied.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(F/K))

/-- The actual finite relation obstruction inflates to the original
restricted-presentation connecting class with the same colimit coefficient map. -/
theorem arithmeticFiniteRelationObstruction_inflation
    (φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep K Ω a ha F)
    (y : groupCohomology B 1) :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
      AlgEquiv.restrictNormalHom F
    let C := arithmeticClassesModOutsideStageRep K Ω a ha F
    let j := coefficientRepresentationColimitOf _
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F
    groupCohomology.map π j 2 ((originalRelationExtensionObstruction B C φ).hom y) =
      (groupCohomology.functor ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) 2).map
        ((Rep.resFunctor π).map φ ≫ j)
        (groupCohomology.δ (originalRelationGroupChange_shortExact π B) 1 2 rfl
          (groupCohomology.map π (𝟙 (Rep.res π B)) 1 y)) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom F
  let C := arithmeticClassesModOutsideStageRep K Ω a ha F
  let D := arithmeticClassesModOutsideColimitRep K Ω a ha
  let j := coefficientRepresentationColimitOf _
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F
  exact congrArg (fun m : groupCohomology B 1 ⟶ groupCohomology D 2 => m.hom y)
    (originalRestrictedRelation_obstruction_inflation π B C D φ j)

end
end Dubon2026
