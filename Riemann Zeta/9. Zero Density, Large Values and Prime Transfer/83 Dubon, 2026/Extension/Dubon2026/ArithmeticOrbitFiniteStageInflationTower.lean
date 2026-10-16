import Dubon2026.ArithmeticOrbitCompletionFiniteStage

/-! # The finite arithmetic stage and original union use the same embedding

The upper finite stage is selected using the original lower coset's
representative. Its literal embedding agrees with the original union
embedding on every stage element. This is the last scalar tower needed
to reuse the existing cocycle-composition theorem for DUB-17's actual
finite-global localization comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The original finite-stage embedding factors through the same original arithmetic-union embedding used by the lower localization cocycle. -/
theorem rationalArithmeticOrbitFiniteStage_inflationTower :
    letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitUpperAlgebra a p hp F c
    letI : Algebra H (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
    letI : SMul H (rationalPrimeLocalClosure p hp) :=
      (arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)).toSMul
    IsScalarTower H (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
  letI : SMul H (rationalPrimeLocalClosure p hp) :=
    (arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)).toSMul
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact rationalArithmeticOrbitEmbedding_mk a p hp H c.out x

end
end Dubon2026
