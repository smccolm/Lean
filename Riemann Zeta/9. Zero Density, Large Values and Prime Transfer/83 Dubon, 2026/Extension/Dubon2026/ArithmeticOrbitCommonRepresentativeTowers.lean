import Dubon2026.ArithmeticOrbitCompletionTower
import Dubon2026.ArithmeticOrbitCosetProjection

/-! # Actual arithmetic completions from one representative

Use the same arithmetic automorphism to select the primes at each field
in a base-change square. The literal embeddings and completed inclusions
then form the towers needed to apply DUB-17's normalized local-degree
formula to the actual auxiliary class.
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
  (σ : rationalArithmeticGaloisGroup a)

/-- The prime at the lifted finite stage lies over precisely the original lower coset's prime. -/
theorem rationalArithmeticOrbitPrime_commonRepresentative_liesOver :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)).asIdeal := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  simpa only [rationalArithmeticOrbitCoset_project_mk a F H hFH σ] using
    rationalArithmeticOrbitPrime_liesOver a p hp F H hFH (QuotientGroup.mk σ)

/-- The actual original completed finite stage forms a tower over the unchanged lower completion inside the local closure. -/
theorem rationalArithmeticOrbitCompletion_commonRepresentative_closureTower :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
        (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
      (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
  let P (d : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) : Prop :=
    ∀ h : (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp F d).asIdeal,
    letI := h
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F d)
        (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ)) :=
      (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F d)
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F d)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk σ))
      (rationalPrimeLocalClosure p hp)
  have ht : P (QuotientGroup.mk
      (QuotientGroup.mk σ : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H).out) := by
    intro h
    exact rationalArithmeticOrbitCompletion_closureTower a p hp F H hFH (QuotientGroup.mk σ)
  exact (Eq.mp (congrArg P (rationalArithmeticOrbitCoset_project_mk a F H hFH σ)) ht)
    (rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ)

omit [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] in
/-- The original lower embedding factors through the actual finite-stage embedding selected by the same lower representative. -/
theorem rationalArithmeticOrbit_commonRepresentative_globalTower :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F (QuotientGroup.mk σ)
    letI : Algebra H (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk σ)
    IsScalarTower F H (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F (QuotientGroup.mk σ)
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk σ)
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (rationalArithmeticOrbitEmbedding_mk a p hp F σ x).trans
    (rationalArithmeticOrbitEmbedding_mk a p hp H σ (IntermediateField.inclusion hFH x)).symm

end
end Dubon2026
