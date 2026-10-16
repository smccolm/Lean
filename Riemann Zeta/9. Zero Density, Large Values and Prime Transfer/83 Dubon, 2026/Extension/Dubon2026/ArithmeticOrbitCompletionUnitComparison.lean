import Dubon2026.ArithmeticOrbitCompletionUnitBaseChange
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Original completion localization is the orbit-field cocycle

The already proved continuous base-change composition applies to the
literal global/completion/orbit maps. Thus the cochain used in DUB-17's
Mackey invariant is the actual global cochain localized at the induced
original finite prime, followed by the proved completion equivalence.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitCompletionGlobalSmul arithmeticOrbitCompletionOrbitSmul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]

/-- The original global unit cocycle, localized at its actual prime and transported through the proved equivalence, is exactly the Mackey orbit-field cocycle. -/
theorem rationalArithmeticOrbitCompletionUnitCocycle_baseChange
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    continuousGaloisUnitBaseChangeCocycle (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitLocalField a p hp F c)
      (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
      (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y) =
        rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  let hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hCompletion : IsScalarTower F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp) := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  let hLocal : IsScalarTower F (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hSameCompletion : IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hSameUpper : IsScalarTower (rationalUnramifiedExtension a)
      (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact @continuousGaloisUnitBaseChangeCocycle_comp F
    (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
    _ _ _ _ _ _
    (arithmeticOrbitCompletionGlobalAlgebra a p hp F c)
    (arithmeticOrbitCompletionTargetAlgebra a p hp F c) (arithmeticOrbitBaseAlgebra a p hp F c)
    F.toAlgebra (arithmeticOrbitBaseClosureAlgebra a p hp F c) (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (arithmeticOrbitCompletionClosureAlgebra a p hp F c) (arithmeticOrbitCompletionClosureAlgebra a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F c).toAlgebra
    (arithmeticOrbitUpperAlgebra a p hp F c) (Algebra.id _) (arithmeticOrbitUpperAlgebra a p hp F c)
    hCompletion hUpper (arithmeticOrbitCompletionClosureTower a p hp F c)
    hSameCompletion hLocal hUpper hSameUpper
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance y

end
end Dubon2026
