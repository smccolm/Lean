import Dubon2026.ArithmeticOrbitFieldBaseChange
import Dubon2026.ArithmeticUnitCorestrictionOrbits

/-! # Actual unit-cocycle base change into an arithmetic orbit field

The original coset embedding and proved scalar towers define genuine
continuous Galois-unit base change. It is the arithmetic map to be
compared with the literal Mackey orbit term on DUB-17's reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalPrimeLocalClosure p hp))]

/-- Genuine continuous unit-cocycle base change for the actual orbit
embedding, using its constructed scalar towers and original Galois fields. -/
def rationalArithmeticOrbitUnitBaseChangeCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo
        (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitLocalField a p hp F c)
          (rationalPrimeLocalClosure p hp)) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalArithmeticOrbitLocalField a p hp F c) :=
    arithmeticOrbitBaseAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : SMul F (rationalArithmeticOrbitLocalField a p hp F c) :=
    (arithmeticOrbitBaseAlgebra a p hp F c).toSMul
  let hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hLocal : IsScalarTower F (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact @continuousGaloisUnitBaseChangeCocycle F (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) _ _ _ _
    (arithmeticOrbitBaseAlgebra a p hp F c) F.toAlgebra
    (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F c).toAlgebra
    (arithmeticOrbitUpperAlgebra a p hp F c) hLocal hUpper
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- The genuine local base change retains the literal embedded unit
and the exact original Galois restriction on both cochain arguments. -/
theorem rationalArithmeticOrbitUnitBaseChangeCocycle_apply
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (g h : Gal(rationalPrimeLocalClosure p hp / rationalArithmeticOrbitLocalField a p hp F c)) :
    (rationalArithmeticOrbitUnitBaseChangeCocycle a p hp F c y).val (g, h) =
      (Units.map (rationalArithmeticOrbitEmbedding a p hp F c).toMonoidHom).toAdditive
        (y.val (rationalArithmeticOrbitBaseChange a p hp F c g,
          rationalArithmeticOrbitBaseChange a p hp F c h)) := rfl

end
end Dubon2026
