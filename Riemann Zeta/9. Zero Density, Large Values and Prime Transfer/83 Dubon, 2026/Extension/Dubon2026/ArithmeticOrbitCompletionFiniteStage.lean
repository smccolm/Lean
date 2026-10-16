import Dubon2026.ArithmeticOrbitCompletionTower
import Dubon2026.ArithmeticOrbitCosetProjection

/-! # Original finite-stage towers for a fixed lower arithmetic coset

Lift the chosen lower representative to the finite upper stage. The
proved quotient projection identity keeps the original lower completion
unchanged, while the literal embedding gives the global tower. These
are the exact towers for DUB-17's finite-global localization consumer.
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
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The prime at the lifted finite stage lies over precisely the original lower coset's prime. -/
theorem rationalArithmeticOrbitPrime_finiteStage_liesOver :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp F c).asIdeal := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH c] using
    rationalArithmeticOrbitPrime_liesOver a p hp F H hFH (QuotientGroup.mk c.out)

/-- The actual original completed finite stage forms a tower over the unchanged lower completion inside the local closure. -/
theorem rationalArithmeticOrbitCompletion_finiteStage_closureTower :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
        (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
      (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out))
      (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI := rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
    (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F c)
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
  let P (d : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) : Prop :=
    ∀ h : (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp F d).asIdeal,
    letI := h
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F d)
        (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out)) :=
      (originalAdicBaseChangeMap F H (rationalArithmeticOrbitPrime a p hp F d)
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out))).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F d)
      (rationalArithmeticOrbitPrimeCompletion a p hp H (QuotientGroup.mk c.out))
      (rationalPrimeLocalClosure p hp)
  have ht : P (QuotientGroup.mk
      (QuotientGroup.mk c.out : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H).out) := by
    intro h
    exact rationalArithmeticOrbitCompletion_closureTower a p hp F H hFH (QuotientGroup.mk c.out)
  exact (Eq.mp (congrArg P (rationalArithmeticOrbitCoset_project_out a F H hFH c)) ht)
    (rationalArithmeticOrbitPrime_finiteStage_liesOver a p hp F H hFH c)

omit [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] in
/-- The original lower embedding factors through the actual finite-stage embedding selected by the same lower representative. -/
theorem rationalArithmeticOrbitFiniteStage_globalTower :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
    letI : Algebra H (rationalPrimeLocalClosure p hp) :=
      arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
    IsScalarTower F H (rationalPrimeLocalClosure p hp) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : Algebra H (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitBaseClosureAlgebra a p hp H (QuotientGroup.mk c.out)
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (rationalArithmeticOrbitEmbedding_mk a p hp H c.out (IntermediateField.inclusion hFH x)).symm

end
end Dubon2026
