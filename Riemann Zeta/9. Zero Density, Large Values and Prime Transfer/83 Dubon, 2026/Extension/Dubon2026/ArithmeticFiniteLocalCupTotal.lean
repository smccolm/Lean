import Dubon2026.OriginalFiniteLocalCocycleTotal
import Dubon2026.ArithmeticFiniteRelationCompletionTotal
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

/-- The actual local Hom-cocycle family constructs one S-place relation
whose actual canonical arithmetic total is the finite sum of the original
local cup invariants on constructed lifts of the restricted global H1 class. -/
theorem arithmeticFiniteLocalCocycles_exists_cup_total
    (S : Finset (HeightOneSpectrum (𝓞 H)))
  (hS : ∀ (σ : Gal(H/F)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv F H σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 F))) (w : T → S)
  [hw : Fact (∀ v : T, originalFinitePrimeBelow F H (w v).val = v.val)]

  (Ω : T → Type) [∀ v, Field (Ω v)]
  [∀ v, Algebra (v.val.adicCompletion F) (Ω v)]
  [∀ v, Algebra ((w v).val.adicCompletion H) (Ω v)]
  [∀ v, IsScalarTower (v.val.adicCompletion F) ((w v).val.adicCompletion H) (Ω v)]
  [∀ v, IsGalois (v.val.adicCompletion F) (Ω v)] [∀ v, IsSepClosed (Ω v)]
  (B : Rep.{0} ℤ Gal(H/F)) [Finite B]
  (c : ∀ v : T, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom F H v.val (w v).val (Ω v) B)) :
    ∃ ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion F H v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion F) ((w v).val.adicCompletion H),
      ∀ y : groupCohomology B 1,
      ∃ x : ∀ v : T, galoisTowerFiniteLocalCoefficientH1 (v.val.adicCompletion F)
        ((w v).val.adicCompletion H) Gal(H/F)
        (originalAdicCompletionGaloisInclusion F H v.val (w v).val) B,
      (∀ v : T, continuousH1ToAlgebraic
        (Rep.res (originalAdicCompletionGaloisInclusion F H v.val (w v).val) B)
        continuous_of_discreteTopology (x v) =
        groupCohomology.map (originalAdicCompletionGaloisInclusion F H v.val (w v).val)
          (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion F H v.val (w v).val) B)) 1 y) ∧
      rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH.out
          ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalSPlaceFullIdeleInclusion F H S hS)
            (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep F H S hS)
              (originalFinitePrimeSPlaceRelation F H S hS T w B
                (fun u => originalAdicUnitRelationMorphism F H u.val (w u).val B (ψ u))) y)) =
        ∑ v : T,
        originalAdicFiniteLocalCupInvariant F H v.val (w v).val (Ω v) B (c v) (x v) := by
  exact originalFiniteLocalCocycles_exists_cup_total F H S hS T w Ω B
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH.out)
    (arithmeticFiniteRelation_completion_total a F H S hS T w Ω B) c

end
end Dubon2026
