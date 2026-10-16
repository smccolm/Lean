import Dubon2026.ArithmeticOrbitCompletionGlobalTowers
import Dubon2026.ArithmeticOrbitUnitBaseChange

/-! # Original global unit cocycles localized at the genuine induced prime

The original global embedding now factors through the actual number-field
completion. Its proved towers define literal Galois restriction and unit
cocycle base change, the localization map needed to identify DUB-17's
Mackey summand with its original finite-prime invariant.
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
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitCompletionGlobalSmul arithmeticOrbitCompletionOrbitSmul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- Genuine Galois restriction through the original prime completion and literal coset-twisted embedding. -/
def rationalArithmeticOrbitCompletionRestriction :
    Gal(rationalPrimeLocalClosure p hp / rationalArithmeticOrbitPrimeCompletion a p hp F c) →*
      Gal(rationalUnramifiedExtension a / F) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  let hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hCompletion : IsScalarTower F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp) := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  exact @galoisBaseChangeRestriction F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) _ _ _ _
    inferInstance F.toAlgebra (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (arithmeticOrbitCompletionClosureAlgebra a p hp F c) (arithmeticOrbitUpperAlgebra a p hp F c)
    hCompletion hUpper inferInstance

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalPrimeLocalClosure p hp))]

/-- The original global cocycle localized through the actual original prime completion. -/
def rationalArithmeticOrbitCompletionUnitCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo
        (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
          (rationalPrimeLocalClosure p hp)) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  let hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hCompletion : IsScalarTower F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp) := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  exact @continuousGaloisUnitBaseChangeCocycle F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) _ _ _ _
    inferInstance F.toAlgebra (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (arithmeticOrbitCompletionClosureAlgebra a p hp F c) (arithmeticOrbitUpperAlgebra a p hp F c)
    hCompletion hUpper inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- The actual completion-localized cochain retains the literal original unit embedding and restriction arguments. -/
theorem rationalArithmeticOrbitCompletionUnitCocycle_apply
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (g h : Gal(rationalPrimeLocalClosure p hp / rationalArithmeticOrbitPrimeCompletion a p hp F c)) :
    (rationalArithmeticOrbitCompletionUnitCocycle a p hp F c y).val (g, h) =
      (Units.map (rationalArithmeticOrbitEmbedding a p hp F c).toMonoidHom).toAdditive
        (y.val (rationalArithmeticOrbitCompletionRestriction a p hp F c g,
          rationalArithmeticOrbitCompletionRestriction a p hp F c h)) := rfl

end
end Dubon2026
