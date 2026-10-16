import Dubon2026.ArithmeticOrbitCompletionStructures

/-! # Literal global scalar towers through the original prime completion

The completion equivalence preserves each original global element, so
the original coset-twisted embedding factors through that completion.
These are the exact towers needed to compare DUB-17's global localization
cocycle with its Mackey orbit-field cocycle.
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

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- Retain the canonical original number-field algebra on its actual adic completion. -/
local instance arithmeticOrbitCompletionGlobalAlgebra :
    Algebra F (rationalArithmeticOrbitPrimeCompletion a p hp F c) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 F) _ _ F F _ _ _ _
    (rationalArithmeticOrbitPrime a p hp F c) (Algebra.id F)

/-- Use exactly the scalar action of the original completed global inclusion. -/
local instance arithmeticOrbitCompletionGlobalSmul :
    SMul F (rationalArithmeticOrbitPrimeCompletion a p hp F c) :=
  (arithmeticOrbitCompletionGlobalAlgebra a p hp F c).toSMul

/-- Use the same literal global scalar action on the orbit field. -/
local instance arithmeticOrbitCompletionOrbitSmul :
    SMul F (rationalArithmeticOrbitLocalField a p hp F c) :=
  (arithmeticOrbitBaseAlgebra a p hp F c).toSMul

/-- The original global inclusion factors through its actual completion and the proved equivalence. -/
theorem rationalArithmeticOrbitCompletion_globalTower :
    IsScalarTower F (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitLocalField a p hp F c) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (rationalArithmeticOrbitCompletionEquiv_algebraMap a p hp F c x).symm)

/-- The same actual coset-twisted closure embedding factors through the genuine original completion. -/
theorem rationalArithmeticOrbitCompletion_globalClosureTower :
    letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
    IsScalarTower F (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  exact IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (rationalArithmeticOrbitCompletionEquiv_coe a p hp F c x).symm)

end
end Dubon2026
