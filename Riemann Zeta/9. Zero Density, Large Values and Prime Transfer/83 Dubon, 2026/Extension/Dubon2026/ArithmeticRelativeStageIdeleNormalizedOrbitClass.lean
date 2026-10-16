import Dubon2026.ArithmeticRelativeStageIdeleOrbitInvariant
import Dubon2026.OriginalFullDecompositionNormalizedIdeleClass

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


/-- The actual orbit-selected full-decomposition prime supplies an original finite-stage idele H2 class with reciprocal global degree and no other finite localization. -/
theorem rationalArithmeticRelativeStageIdeleOrbitInvariant_exists_normalized
    (n : ℕ)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = n)
    (hw : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      OriginalFiniteDecompositionGroup F H
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) = ⊤) :
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp F H hFH c x =
        (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
        ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
          t ≠ rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out) →
            originalFullIdeleAdicH2 F H t x = 0) := by
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
  obtain ⟨x, hx, hs⟩ := originalFullDecomposition_exists_normalized_idele_class F H
    (rationalArithmeticOrbitPrime a p hp F c)
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))
    (rationalPrimeLocalClosure p hp) hw
  refine ⟨x, ?_, hs⟩
  exact hx.trans (congrArg (fun k : ℕ => (↑((1 : ℚ) / k) : AddCircle (1 : ℚ))) hdegree)

end
end Dubon2026
