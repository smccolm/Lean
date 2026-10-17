import Dubon2026.ArithmeticRealOrbitFiniteEmbedding
import Dubon2026.ContinuousDiscreteH2Comparison

/-! # Original infinite localization kills the actual real orbit cocycle

The specified finite-stage cocycle is inflated into the same arithmetic
union and then used by the actual real Mackey construction. Its algebraic
class factors through the original infinite completion by the derived
field square. Since the real stabilizer is discrete, the existing
continuous/algebraic H2 comparison transfers vanishing back to the genuine
continuous orbit term. This removes DUB-17's real-orbit kernel obstacle.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  arithmeticRealGlobalClosureAlgebra arithmeticRealGlobalClosureSMul arithmeticRealGlobalClosureTower
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticRealOrbitUpperGalois

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (H : IntermediateField ℚ (rationalUnramifiedExtension a))
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]
  (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup)

/-- The actual real Mackey orbit of the literal finite-stage inflation
has precisely the original field-embedding cocycle, on the same values. -/
theorem rationalArithmeticRealOrbitFiniteCocycle_comparison
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsGalois F H := hGal
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
    (rationalArithmeticRealOrbitUnitCocycle a F c
      (@rationalArithmeticRelativeStageInflation a F H hFH hGal y)).val =
        groupCohomology.mapCocycles₂ (rationalArithmeticRealOrbitFiniteRestriction a F c H hFH)
          (originalInfiniteEmbeddingFieldRepHom F H (ArithmeticRealOrbitStabilizer a F c)
            (rationalArithmeticRealOrbitFiniteEmbedding a F c H)
            (rationalArithmeticRealOrbitFiniteRestriction a F c H hFH)
            (ArithmeticRealOrbitStabilizer a F c).subtype
            (rationalArithmeticRealOrbitFiniteEmbedding_equivariant a F c H hFH)) z.val := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : IsGalois F H := hGal
  letI : IsScalarTower F H (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  apply Subtype.ext
  funext de
  apply congrArg Additive.ofMul
  apply Units.ext
  rfl

/-- Vanishing of the original finite-stage infinite localizations kills
the actual continuous real orbit of its literal arithmetic inflation. -/
theorem rationalArithmeticRealOrbitUnitCocycle_eq_zero_of_infinite
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (hy : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
      ∀ v : NumberField.InfinitePlace H,
        originalGlobalInfiniteH2 F H v (groupCohomology.H2π _ z.val) = 0) :
    (Submodule.Quotient.mk (rationalArithmeticRealOrbitUnitCocycle a F c
      (@rationalArithmeticRelativeStageInflation a F H hFH hGal y)) :
      ContinuousRepresentationH2
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℝ ℂ) (ArithmeticRealOrbitStabilizer a F c).subtype)
        (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits ℝ ℂ)
          (ArithmeticRealOrbitStabilizer a F c).subtype continuous_subtype_val
          (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ)))) = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : IsGalois F H := hGal
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  let A := restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℝ ℂ)
    (ArithmeticRealOrbitStabilizer a F c).subtype
  let hA := restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits ℝ ℂ)
    (ArithmeticRealOrbitStabilizer a F c).subtype continuous_subtype_val
    (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ))
  apply continuousH2ToAlgebraic_injective A hA
  rw [map_zero, continuousH2ToAlgebraic_mk]
  rw [rationalArithmeticRealOrbitFiniteCocycle_comparison a F H hFH c y]
  rw [← groupCohomology.H2π_comp_map_apply]
  exact originalInfiniteEmbeddingH2_zero F H (ArithmeticRealOrbitStabilizer a F c)
    (rationalArithmeticRealOrbitFiniteEmbedding a F c H)
    (rationalArithmeticRealOrbitFiniteRestriction a F c H hFH)
    (ArithmeticRealOrbitStabilizer a F c).subtype
    (rationalArithmeticRealOrbitFiniteEmbedding_equivariant a F c H hFH)
    (groupCohomology.H2π _ z.val) (hy _)

end
end Dubon2026
