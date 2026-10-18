import Dubon2026.ArithmeticCommonStagePrimeClassZero
import Dubon2026.OriginalSPlaceFullClassImage
import Dubon2026.ArithmeticSPlaceFiniteStages

/-! The finite relation-morphism route to DUB-17's local pairing criterion.
Apply the proved total-zero class theorem directly to the original relation
connecting class in S-place ideles. Local realization can therefore use
finite relation morphisms without an additional source-Hom H1 isomorphism. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The canonical total of the actual S-place relation connecting class
detects its original outside-unit class obstruction. Its full-class
prime annihilator and all Sylow normalization inputs are derived. -/
theorem arithmeticSPlaceRelationObstruction_zero_of_total_zero
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (M : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (B : Rep.{0} ℤ Gal(M/ℚ)) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a) (hB : ∀ b : B, p • b = 0)
    (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha M)
    (y : groupCohomology B 1) :
    let S := arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha M
    let hS := originalExceptionalIntegerSupport_galoisStable M ℚ a ha
    let J := ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha M
    let C := originalIdeleClassesModOutsideRep ℚ M S hS
    let u := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map
      (originalSPlaceFullIdeleInclusion ℚ M S hS)
      ((originalRelationExtensionObstruction B J φ).hom y)
    arithmeticCommonStageRationalIdeleTotal a M u = 0 →
      (originalRelationExtensionObstruction B C
        (φ ≫ originalSPlaceIdeleClassRepHom ℚ M S hS ≫ originalSPlaceClassComparison ℚ M S hS)).hom y = 0 := by
  intro S hS J C u htotal
  let v := (originalRelationExtensionObstruction B J φ).hom y
  let incl := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalSPlaceFullIdeleInclusion ℚ M S hS)
  let π := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
  have hv : p • v = 0 := originalRelationExtensionObstruction_nsmul_zero B J p hB φ y
  have hu : p • u = 0 := (map_nsmul incl.hom p v).symm.trans
    ((congrArg incl hv).trans (map_zero incl.hom))
  have hc : p • π u = 0 := (map_nsmul π.hom p u).symm.trans
    ((congrArg π hu).trans (map_zero π.hom))
  have hzero := arithmeticCommonStageIdele_class_zero_of_total_zero a M p hp2 hpa u hc htotal
  have hcomparison := originalSPlaceFullIdele_H2_class_comparison ℚ M S hS v
  have hob : (originalRelationExtensionObstruction B C
      (φ ≫ originalSPlaceIdeleClassRepHom ℚ M S hS ≫ originalSPlaceClassComparison ℚ M S hS)).hom y =
      (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalSPlaceClassComparison ℚ M S hS)
        ((groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalSPlaceIdeleClassRepHom ℚ M S hS) v) := by
    change (groupCohomology.functor ℤ Gal(M/ℚ) 2).map
      (φ ≫ originalSPlaceIdeleClassRepHom ℚ M S hS ≫ originalSPlaceClassComparison ℚ M S hS)
      ((groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl).hom y) = _
    simp only [Functor.map_comp]
    rfl
  exact hob.trans (hcomparison.trans
    ((congrArg ((groupCohomology.functor ℤ Gal(M/ℚ) 2).map
      (originalIdeleClassesModOutsideRepHom ℚ M S hS)) hzero).trans
        (map_zero ((groupCohomology.functor ℤ Gal(M/ℚ) 2).map
          (originalIdeleClassesModOutsideRepHom ℚ M S hS)).hom)))

end
end Dubon2026
