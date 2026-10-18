import Dubon2026.OriginalFiniteLocalCocycleTotal
import Dubon2026.OriginalAdicFiniteCupInvariant
import Dubon2026.ArithmeticFiniteRelationTotalSupport
import Dubon2026.ArithmeticRelativePrimeCompletionComparison

/-! The actual arithmetic canonical total of the constructed finite relation
is the sum of its original continuous local cup invariants. All coordinate,
finite-H1-lift and support obligations are derived. This supplies the
canonical-total edge in DUB-17 reverse localization; specializing its
coefficients to the actual arithmetic Cartier family remains a separate edge. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [-instance] UniformSpace.Completion.instSMul
  SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul finitePrimeRelationCosets finiteLocalRelationFamilyLiesOver
  originalCompletionCarryValuation originalCompletionCarryLocalField
  finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] [hFH : Fact (F ≤ H)]
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH.out).toAlgebra
    IsGalois F H]

attribute [local instance] finiteRelationTotalStageAlgebra finiteRelationTotalStageModule
  finiteRelationTotalStageSMul finiteRelationTotalStageTower finiteRelationTotalStageFinite
  finiteRelationTotalStageGalois

variable (S : Finset (HeightOneSpectrum (𝓞 H)))
  (hS : ∀ (σ : Gal(H/F)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv F H σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 F))) (w : T → S)
  [hw : Fact (∀ v : T, originalFinitePrimeBelow F H (w v).val = v.val)]

  (Ω : T → Type) [∀ v, Field (Ω v)]
  [∀ v, Algebra (v.val.adicCompletion F) (Ω v)]
  [∀ v, Algebra ((w v).val.adicCompletion H) (Ω v)]
  [∀ v, IsScalarTower (v.val.adicCompletion F) ((w v).val.adicCompletion H) (Ω v)]
  [∀ v, IsGalois (v.val.adicCompletion F) (Ω v)] [∀ v, IsSepClosed (Ω v)]
  (B : Rep.{0} ℤ Gal(H/F))

/-- Native prime realization and the proved support of the actual relation
identify its canonical arithmetic total with its original completion sum. -/
theorem arithmeticFiniteRelation_completion_total
    (ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion F H v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion F) ((w v).val.adicCompletion H))
    (y : groupCohomology B 1) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH.out ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalSPlaceFullIdeleInclusion F H S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep F H S hS)
            (originalFinitePrimeSPlaceRelation F H S hS T w B
              (fun u => originalAdicUnitRelationMorphism F H u.val (w u).val B (ψ u))) y)) =
      ∑ v : T, originalFullIdeleCompletionInvariant F H v.val (w v).val (Ω v) ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalSPlaceFullIdeleInclusion F H S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep F H S hS)
            (originalFinitePrimeSPlaceRelation F H S hS T w B
              (fun u => originalAdicUnitRelationMorphism F H u.val (w u).val B (ψ u))) y)) := by
  let φ := fun v : T => originalAdicUnitRelationMorphism F H v.val (w v).val B (ψ v)
  let Φ := originalFinitePrimeSPlaceRelation F H S hS T w B φ
  let u := (groupCohomology.functor ℤ Gal(H/F) 2).map (originalSPlaceFullIdeleInclusion F H S hS)
    (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep F H S hS) Φ y)
  have hsum := arithmeticFiniteRelation_total_eq_sum a F H S hS T w B hw.out φ y
  refine hsum.trans ((Finset.sum_coe_sort T
    (fun v => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH.out v u)).symm.trans ?_)
  exact Finset.sum_congr rfl (fun v _ =>
    rationalArithmeticRelativeStage_prime_invariant_realization a F H hFH.out
      v.val (w v).val (Ω v) u)

end
end Dubon2026
