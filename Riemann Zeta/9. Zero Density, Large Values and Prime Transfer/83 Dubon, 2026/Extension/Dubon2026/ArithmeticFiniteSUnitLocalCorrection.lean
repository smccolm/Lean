import Dubon2026.ArithmeticSPlaceLocalMap
import Dubon2026.ArithmeticPrimeUnitDualConnecting
import Dubon2026.OriginalDualConnectingFreeCorrection

/-! Project the finite S-unit correction to its actual original prime.
The local free correction then has zero dual connecting class. This is
the correction-removal step in DUB-17's prescribed local recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ))
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- The genuine finite correction retains its free-correction equation
under the constructed original-prime localization morphism. -/
theorem arithmeticFiniteSUnitCorrection_local_relation
    (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (l : Rep.free ℤ Gal(F/ℚ) B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (hη : η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F =
      φ - originalRelationInclusion B ≫ l) :
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let J := rationalArithmeticSPlaceLocalMorphism a ha F p
    let X := arithmeticPrimeLocalRelationPresentation a F B p.val.val p.val.property
    (Rep.resFunctor π).map (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫ J =
      (Rep.resFunctor π).map φ ≫ J - X.f ≫ ((Rep.resFunctor π).map l ≫ J) := by
  intro π J X
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h := congrArg (fun m => m.hom x) hη
  exact (congrArg J.hom h).trans (map_sub J.hom _ _)

end
end Dubon2026
