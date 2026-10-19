import Dubon2026.RationalArithmeticOriginalPrimeTower
import Dubon2026.OriginalFiniteAdeleBaseChange

/-! The selected original prime completions retain their literal scalar
tower inside the same local closure. DUB-17 uses this to compare the prime
value of the finite correction before and after field enlargement. -/
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
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)

/-- The original upper prime lies over the selected lower arithmetic prime. -/
theorem rationalArithmeticOriginalPrime_liesOver :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    (rationalArithmeticOriginalPrime a p hp L).asIdeal.LiesOver
      (rationalArithmeticOriginalPrime a p hp M).asIdeal := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  have h := originalFinitePrimeBelow_liesOver M L (rationalArithmeticOriginalPrime a p hp L)
  simpa only [rationalArithmeticOriginalPrime_under a p hp M L hML] using h

/-- The existing completed orbit tower specializes to the exact chosen
arithmetic completions, with the original completed field inclusion. -/
theorem rationalArithmeticOriginalCompletion_finiteTower :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI := rationalArithmeticOriginalPrime_liesOver a p hp M L hML
    letI : Algebra ((rationalArithmeticOriginalPrime a p hp M).adicCompletion M)
        ((rationalArithmeticOriginalPrime a p hp L).adicCompletion L) :=
      (originalAdicBaseChangeMap M L (rationalArithmeticOriginalPrime a p hp M)
        (rationalArithmeticOriginalPrime a p hp L)).toAlgebra
    IsScalarTower ((rationalArithmeticOriginalPrime a p hp M).adicCompletion M)
      ((rationalArithmeticOriginalPrime a p hp L).adicCompletion L) (rationalPrimeLocalClosure p hp) := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  let P (c : rationalArithmeticGaloisGroup a ⧸
      rationalArithmeticOrbitFixingSubgroup a M.toIntermediateField) : Prop :=
    ∀ h : (rationalArithmeticOriginalPrime a p hp L).asIdeal.LiesOver
      (rationalArithmeticOrbitPrime a p hp M.toIntermediateField c).asIdeal,
    letI := h
    letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp M.toIntermediateField c)
        ((rationalArithmeticOriginalPrime a p hp L).adicCompletion L) :=
      (originalAdicBaseChangeMap M L (rationalArithmeticOrbitPrime a p hp M.toIntermediateField c)
        (rationalArithmeticOriginalPrime a p hp L)).toAlgebra
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp M.toIntermediateField c)
      ((rationalArithmeticOriginalPrime a p hp L).adicCompletion L) (rationalPrimeLocalClosure p hp)
  have hc := rationalArithmeticIdentityCoset_tower a M L hML
  dsimp only at hc
  have hP : P (QuotientGroup.mk (Quotient.out
      (QuotientGroup.mk (1 : rationalArithmeticGaloisGroup a) :
        rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a L.toIntermediateField))) := by
    intro h
    exact rationalArithmeticOrbitCompletion_closureTower a p hp M.toIntermediateField L.toIntermediateField
      hML (QuotientGroup.mk 1)
  rw [hc] at hP
  exact hP (rationalArithmeticOriginalPrime_liesOver a p hp M L hML)

end
end Dubon2026
