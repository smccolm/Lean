import Dubon2026.OriginalLocalCompletionMapTower
import Dubon2026.ArithmeticOrbitPrimeContraction
import Dubon2026.ArithmeticOrbitCompletionGlobalTowers

/-! # The original completed arithmetic tower inside the local closure

The proved literal local inclusion and completion-map comparison derive
the actual original completed tower. These are the scalar compatibility
premises needed to apply the finite-global invariant comparison to
DUB-17's original Mackey localization, with no assumed tower certificate.
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
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H)

/-- The actual upper arithmetic prime lies over the original lower prime of the projected representative. -/
theorem rationalArithmeticOrbitPrime_liesOver :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    (rationalArithmeticOrbitPrime a p hp H c).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out)).asIdeal := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact originalLocalEmbeddingPrime_liesOver F H
    (rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitLocalField a p hp H c) p hp
    (rationalArithmeticOrbitSubfieldMap a p hp F H hFH c)
    (rationalArithmeticOrbitSubfieldMap_global a p hp F H hFH c)

/-- The constructed actual completion equivalences commute with the original completed number-field inclusion. -/
theorem rationalArithmeticOrbitCompletionEquiv_tower
    (x : rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI := rationalArithmeticOrbitPrime_liesOver a p hp F H hFH c
    rationalArithmeticOrbitSubfieldMap a p hp F H hFH c
      (rationalArithmeticOrbitCompletionEquiv a p hp F (QuotientGroup.mk c.out) x) =
      rationalArithmeticOrbitCompletionEquiv a p hp H c
        (originalAdicBaseChangeMap F H
          (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out))
          (rationalArithmeticOrbitPrime a p hp H c) x) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI := rationalArithmeticOrbitPrime_liesOver a p hp F H hFH c
  exact originalLocalCompletionMap_tower F H
    (rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitLocalField a p hp H c) p hp
    (rationalArithmeticOrbitSubfieldMap a p hp F H hFH c)
    (rationalArithmeticOrbitSubfieldMap_global a p hp F H hFH c) x

/-- The same original finite-prime completions form the literal scalar tower in the actual local closure. -/
theorem rationalArithmeticOrbitCompletion_closureTower :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI := rationalArithmeticOrbitPrime_liesOver a p hp F H hFH c
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
        (rationalArithmeticOrbitPrimeCompletion a p hp H c) :=
      (originalAdicBaseChangeMap F H
        (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out))
        (rationalArithmeticOrbitPrime a p hp H c)).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
      (rationalArithmeticOrbitPrimeCompletion a p hp H c) (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI := rationalArithmeticOrbitPrime_liesOver a p hp F H hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
      (rationalArithmeticOrbitPrimeCompletion a p hp H c) :=
    (originalAdicBaseChangeMap F H
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out))
      (rationalArithmeticOrbitPrime a p hp H c)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact congrArg Subtype.val (rationalArithmeticOrbitCompletionEquiv_tower a p hp F H hFH c x)

end
end Dubon2026
