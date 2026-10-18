import Dubon2026.ArithmeticRationalIdeleTotalFinsum
import Dubon2026.ArithmeticRationalPrimeCompletionComparison
import Dubon2026.OriginalIndexedRelationInvariantSum
import Dubon2026.RationalArithmeticOriginalCompletionRestriction

/-! The canonical rational arithmetic total of the actual indexed relation.
The arithmetic realization and prime reindexing discharge the generic
normalization premises; actual relation coordinates discharge support.
This is the rational-base finite total needed by DUB-17's Cartier family. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV1 Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra
  arithmeticOrbitCompletionNumberField indexedPrimeRelationCosets rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (S : Finset (HeightOneSpectrum (𝓞 F)))
  (hS : ∀ (σ : Gal(F/ℚ)) t, t ∈ S ↔ numberFieldGaloisPlaceEquiv ℚ F σ t ∈ S)
  (I : Type) [Fintype I] (v : I → HeightOneSpectrum (𝓞 ℚ)) (w : I → S)
  (B : Rep.{0} ℤ Gal(F/ℚ))

/-- The actual canonical rational total is the finite sum of its original
prime coordinates, with all support and normalization premises discharged. -/
theorem arithmeticRationalIndexedRelation_total_eq_sum
    (hv : Function.Injective v)
    (hw : ∀ i : I, originalFinitePrimeBelow ℚ F (w i).val = v i)
    (φ : ∀ i : I,
      Rep.res (OriginalFiniteDecompositionGroup ℚ F (w i).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep ℚ F (w i).val)
    (y : groupCohomology B 1) :
    let u := (groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalSPlaceFullIdeleInclusion ℚ F S hS)
      (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep ℚ F S hS)
        (originalIndexedPrimeSPlaceRelation ℚ F S hS I w B φ) y)
    arithmeticCommonStageRationalIdeleTotal a F u =
      ∑ i : I, arithmeticCommonStageRationalPrimeInvariant a F (v i) u := by
  intro u
  have hcanon := arithmeticCommonStageRationalIdeleTotal_eq_finsum a F u
  have hindexed := originalIndexedRelation_invariants_finsum_eq_sum ℚ F S hS I v w B
    (arithmeticCommonStageRationalPrimeInvariant a F)
    (arithmeticCommonStageRationalPrimeInvariant_realization a F) hv hw φ y
  with_reducible_and_instances exact hcanon.trans hindexed

end
end Dubon2026
