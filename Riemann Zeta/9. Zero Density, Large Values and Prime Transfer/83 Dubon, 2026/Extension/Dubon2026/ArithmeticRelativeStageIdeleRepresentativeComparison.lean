import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeInvariant
import Dubon2026.ArithmeticRelativeStageIdeleOrbitInvariant
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport
import Dubon2026.ArithmeticOrbitCommonRepresentativeTowers
import Dubon2026.ArithmeticRelativeStageIdeleCohomology
import Dubon2026.ArithmeticOrbitRelativeStageLocalizationInvariant
import Dubon2026.ArithmeticOrbitCompletionInvariantTerm
import Dubon2026.OriginalFullIdeleCompletionInvariant

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitCompletionGlobalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

attribute [local instance] arithmeticRelativeStageIdeleAddCommGroup arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

/-- Choosing the original lower coset's representative recovers exactly its canonical full-idele orbit invariant. -/
theorem rationalArithmeticRelativeStageIdeleRepresentativeInvariant_out :
    rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH c.out =
      rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp F H hFH c := by
  apply AddMonoidHom.ext
  intro x
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH c.out
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out))
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H hFH c
  letI := rationalArithmeticOrbitCompletion_commonRepresentative_closureTower a p hp F H hFH c.out
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk c.out))
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  have hc : (QuotientGroup.mk c.out :
      rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) = c :=
    Quotient.out_eq' c
  exact originalFullIdeleCompletionInvariant_eq_of_primes F H
    (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))
    (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
    (congrArg (rationalArithmeticOrbitPrime a p hp F) hc) rfl x

end
end Dubon2026
