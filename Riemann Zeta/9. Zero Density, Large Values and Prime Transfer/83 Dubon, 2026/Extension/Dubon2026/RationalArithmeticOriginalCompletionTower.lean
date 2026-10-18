import Dubon2026.RationalOriginalCompletionInvariant
import Dubon2026.ArithmeticOrbitCompletionTower
import Dubon2026.OriginalAdicUnitRelationTransport

/-! Retain the original rational prime-local closure while using the
genuine number-field completions in the finite relation construction.
Native completion-map naturality constructs the scalar tower. This is
the field-map input to DUB-17's actual arithmetic H1/Cartier comparison. -/
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
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The original identity coset selects the completion attached to the
specified arithmetic embedding of the finite field. -/
abbrev rationalArithmeticOriginalPrime :=
  rationalArithmeticOrbitPrime a p hp F.toIntermediateField (QuotientGroup.mk 1)

/-- This upper prime lies over the original ring-of-integers prime of Q. -/
local instance rationalArithmeticOriginalPrimeLiesOver :
    (rationalArithmeticOriginalPrime a p hp F).asIdeal.LiesOver
      (rationalOriginalPrimePlace p hp).asIdeal := by
  let E := rationalArithmeticOrbitLocalField a p hp F.toIntermediateField (QuotientGroup.mk 1)
  exact originalLocalEmbeddingPrime_liesOver ℚ F (rationalPrimeLocalField p hp) E p hp
    (Algebra.ofId (rationalPrimeLocalField p hp) E)
    (fun x => by simp only [eq_ratCast, map_ratCast])

attribute [local instance] originalAdicRelationCompletionAlgebra

/-- The original two completion maps preserve every element of the same
completed rational base, by native completion extensionality. -/
theorem rationalArithmeticOriginalCompletion_tower_map
    (x : (rationalOriginalPrimePlace p hp).adicCompletion ℚ) :
    rationalArithmeticOrbitCompletionEquiv a p hp F.toIntermediateField (QuotientGroup.mk 1)
      (originalAdicBaseChangeMap ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F) x) =
      algebraMap (rationalPrimeLocalField p hp)
        (rationalArithmeticOrbitLocalField a p hp F.toIntermediateField (QuotientGroup.mk 1))
        (rationalOriginalPrimeCompletionEquiv p hp x) := by
  let E := rationalArithmeticOrbitLocalField a p hp F.toIntermediateField (QuotientGroup.mk 1)
  letI : NontriviallyNormedField E := localFieldOriginalNorm E
  change originalLocalCompletionMap F E p hp
    (originalAdicBaseChangeMap ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F) x) =
    algebraMap (rationalPrimeLocalField p hp) E
      (originalLocalCompletionMap ℚ (rationalPrimeLocalField p hp) p hp x)
  apply UniformSpace.Completion.ext'
    ((originalLocalCompletionMap_continuous F E p hp).comp
      (originalAdicBaseChangeMap_continuous ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)))
    ((originalLocalScalar_continuous (rationalPrimeLocalField p hp) E).comp
      (originalLocalCompletionMap_continuous ℚ (rationalPrimeLocalField p hp) p hp))
  intro z
  change originalLocalCompletionMap F E p hp
    (originalAdicBaseChangeMap ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)
      (algebraMap ℚ ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) z.ofVal)) =
    algebraMap (rationalPrimeLocalField p hp) E
      (originalLocalCompletionMap ℚ (rationalPrimeLocalField p hp) p hp
        (algebraMap ℚ ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) z.ofVal))
  rw [originalAdicBaseChangeMap_algebraMap]
  exact (originalLocalCompletionMap_algebraMap F E p hp (algebraMap ℚ F z.ofVal)).trans
    ((show algebraMap F E (algebraMap ℚ F z.ofVal) =
        algebraMap (rationalPrimeLocalField p hp) E
          (algebraMap ℚ (rationalPrimeLocalField p hp) z.ofVal) by
        simp only [eq_ratCast, map_ratCast]).trans
      (congrArg (algebraMap (rationalPrimeLocalField p hp) E)
        (originalLocalCompletionMap_algebraMap ℚ (rationalPrimeLocalField p hp) p hp z.ofVal).symm))

/-- The actual finite completion and the original prime-local closure
form the literal tower over the original rational number-field completion. -/
theorem rationalArithmeticOriginalCompletion_closureTower :
    IsScalarTower ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
      (rationalPrimeLocalClosure p hp) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (congrArg Subtype.val (rationalArithmeticOriginalCompletion_tower_map a p hp F x)).symm

end
end Dubon2026
