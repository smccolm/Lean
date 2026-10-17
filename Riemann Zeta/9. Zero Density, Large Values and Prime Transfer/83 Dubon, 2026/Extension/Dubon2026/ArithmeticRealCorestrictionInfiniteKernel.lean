import Dubon2026.ArithmeticRealOrbitInfiniteVanishing
import Dubon2026.OriginalIdeleInfiniteH2

/-! # Original infinite vanishing kills real field corestriction

The exact Mackey sum and the original completion comparison now apply
to the same finite-stage cocycle and its literal arithmetic inflation.
Every real orbit trace vanishes, so the actual real restriction of genuine
field corestriction is zero. This is the real kernel condition needed to
use the proved prime-power sum for DUB-17's full-order class witness.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic arithmeticRealGlobalClosureAlgebra arithmeticRealGlobalClosureSMul
  arithmeticRealGlobalClosureTower arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete
  arithmeticRealOrbitUpperGalois arithmeticRealOrbitGlobalFinite arithmeticRealOrbitGlobalFintype
  arithmeticRealOrbitIndexFinite arithmeticRealOrbitIndexFintype
  arithmeticRealOrbitStabilizerFintype arithmeticRealOrbitStabilizerFamily

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Every actual real orbit trace of the same inflation vanishes when
the original finite-stage infinite localizations vanish. -/
theorem rationalArithmeticRealOrbitUnitTrace_eq_zero_of_infinite
    (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup)
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      ∀ v : NumberField.InfinitePlace H,
        originalGlobalInfiniteH2 F H v (groupCohomology.H2π _ z.val) = 0) :
    rationalArithmeticRealOrbitUnitTrace a F c
      (@rationalArithmeticRelativeStageInflation a F H hFH hGal y) = 0 := by
  let f := continuousRepresentationH2Corestriction (Rep.ofAlgebraAutOnUnits ℝ ℂ)
    (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ))
    (ArithmeticRealOrbitStabilizer a F c)
    (cosetOrbitStabilizer_isOpen _
      (galoisBaseChangeRestriction_continuous ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup F.fixingSubgroup_isOpen c)
  have hz := rationalArithmeticRealOrbitUnitCocycle_eq_zero_of_infinite a F H hFH c y hy
  exact (congrArg f hz).trans (map_zero f)

/-- Original infinite-place vanishing forces the actual real restriction
of genuine field corestriction of the same inflated finite-stage class to vanish. -/
theorem rationalArithmeticRealCorestriction_eq_zero_of_infinite
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      ∀ v : NumberField.InfinitePlace H,
        originalGlobalInfiniteH2 F H v (groupCohomology.H2π _ z.val) = 0) :
    rationalArithmeticRealUnitH2Restriction a
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
        (Submodule.Quotient.mk (@rationalArithmeticRelativeStageInflation a F H hFH hGal y))) = 0 := by
  exact (rationalArithmeticUnitCorestriction_realRestriction a F _).trans
    (Finset.sum_eq_zero (fun ω _ =>
      rationalArithmeticRealOrbitUnitTrace_eq_zero_of_infinite a F H hFH ω.out y hy))

end
end Dubon2026
