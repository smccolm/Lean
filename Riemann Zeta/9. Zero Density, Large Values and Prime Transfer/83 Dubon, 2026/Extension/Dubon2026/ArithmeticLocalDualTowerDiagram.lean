import Dubon2026.OriginalContravariantHomPrecompositionDiagram
import Dubon2026.ArithmeticPrimeUnitDualConnecting
import Dubon2026.OriginalGaloisRestrictionTowerDiagram
import Dubon2026.RationalTraceFiniteTowerAction

/-! Dualize the repository's actual finite-field relation tower at the
chosen arithmetic prime. This is the concrete diagram required to compare
the finite correction's local class in DUB-17. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois

variable (a : 𝓞 ℚ)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) (p : ℕ) (hp : p.Prime)

/-- The original tower induces this specific map of local dual sequences. -/
def arithmeticLocalDualTowerDiagram :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    arithmeticPrimeLocalUnitDualSequence a M B p hp ⟶
      arithmeticPrimeLocalUnitDualSequence a L (Rep.res τ B) p hp := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  letI : IsScalarTower ℚ M L := IsScalarTower.of_algHom (IntermediateField.inclusion hML)
  letI : IsScalarTower M L (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  let D := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  let XM := arithmeticPrimeLocalRelationPresentation a M B p hp
  let XL := arithmeticPrimeLocalRelationPresentation a L (Rep.res τ B) p hp
  exact originalContravariantHomPrecompositionDiagram XL XM D
    ((Rep.resFunctor j).mapShortComplex.map
      (originalGaloisRelationTowerMap ℚ M L (rationalUnramifiedExtension a) B))

end
end Dubon2026
