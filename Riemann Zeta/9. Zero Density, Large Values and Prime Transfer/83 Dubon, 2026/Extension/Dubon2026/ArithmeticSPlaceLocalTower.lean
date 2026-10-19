import Dubon2026.ArithmeticSPlaceLocalMap
import Dubon2026.OriginalSPlaceBaseChangeFiniteValue
import Dubon2026.RationalArithmeticOriginalCompletionFiniteTower

/-! The actual finite S-place transition preserves its original prime-unit
value in the fixed local closure. DUB-17 needs this exact comparison to
identify the corrected relation with the original source-local relation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- The same S-place unit has the same actual local value after the
original finite-field transition. The chosen primes and completed field
embeddings are identified by the proved original arithmetic tower. -/
theorem rationalArithmeticSPlaceLocalMap_tower
    (x : ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha M) :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    rationalArithmeticSPlaceLocalMap a ha L p
      ((arithmeticSPlaceFiniteTransition ℚ (AlgebraicClosure ℚ) a ha M L hML).hom x) =
        rationalArithmeticSPlaceLocalMap a ha M p x := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  let v := rationalExceptionalIndexedUpperPrime a ha M p
  let w := rationalExceptionalIndexedUpperPrime a ha L p
  let V := v.val.adicCompletion M
  let W := w.val.adicCompletion L
  let Ω := rationalPrimeLocalClosure p.val.val p.val.property
  letI := rationalArithmeticOriginalPrime_liesOver a p.val.val p.val.property M L hML
  letI : Algebra V W := (originalAdicBaseChangeMap M L v.val w.val).toAlgebra
  letI := rationalArithmeticOriginalCompletion_finiteTower a p.val.val p.val.property M L hML
  have h := originalSPlaceBaseChange_finite_value_at M L
    (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha M)
    (arithmeticSUnitFiniteStageSupport ℚ (AlgebraicClosure ℚ) a ha L)
    (arithmeticSPlaceFiniteStage_support ℚ (AlgebraicClosure ℚ) a ha M L hML)
    x v w (rationalArithmeticOriginalPrime_under a p.val.val p.val.property M L hML)
  apply Additive.toMul.injective
  apply Units.ext
  exact (congrArg (algebraMap W Ω) h).trans
    (IsScalarTower.algebraMap_apply V W Ω ((x (Sum.inr v)).toMul.val)).symm

end
end Dubon2026
