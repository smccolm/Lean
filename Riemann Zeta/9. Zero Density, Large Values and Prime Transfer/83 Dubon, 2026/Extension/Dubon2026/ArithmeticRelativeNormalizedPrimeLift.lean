import Dubon2026.ArithmeticRelativeStageIdeleOrbitInvariant
import Dubon2026.OriginalSinglePrimeNormalizedLocalLift

/-! # Normalized local trace lift at the actual orbit-selected prime

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The exact local trace normalization statement, retaining the original local class, genuine trace lift and supplied prime invariant; this proposition alone asserts no existence. -/
def OriginalLocalTraceNormalization
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (invariant : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
      invariant (originalSinglePrimeIdeleH2Lift K L w y) =
        (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ))

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


/-- The original orbit-selected prime has a constructed local class whose genuine trace lift is normalized by the actual decomposition degree. -/
theorem rationalArithmeticRelativeStage_exists_normalized_local_trace
    : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalTraceNormalization F H
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))
      (rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp F H hFH c) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitFiniteStage_globalTower a p hp F H hFH c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp F c
  letI := rationalArithmeticOrbitCompletion_globalClosureTower a p hp H (QuotientGroup.mk c.out)
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
  letI := rationalArithmeticOrbitCompletion_finiteStage_closureTower a p hp F H hFH c
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩
  let w := rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)
  exact originalSinglePrime_exists_normalized_local_lift F H
    (rationalArithmeticOrbitPrime a p hp F c) w (rationalPrimeLocalClosure p hp)

end
end Dubon2026
