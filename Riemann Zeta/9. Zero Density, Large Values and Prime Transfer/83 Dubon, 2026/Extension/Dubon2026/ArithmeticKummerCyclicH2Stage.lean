import Dubon2026.ArithmeticKummerUnitH2FiniteStage
import Dubon2026.OriginalUnramifiedCyclicH2Stage

/-! # The exact arithmetic Kummer class descends to a constructed cyclic stage

This consumes the original cyclotomic arithmetic class used by the trace
cup and finite invariant sum. Its actual Kummer image, coefficient-prime
torsion, finite presentation, ambient containment and cyclic descent are
all derived. The remaining DUB-17 sum-zero obligation is the actual
cyclotomic principal product and arithmetic/local completion comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete

/-- Retain the rational algebra of the frozen original arithmetic ambient closure. -/
local instance arithmeticCyclicAmbientAlgebra : Algebra ℚ (AlgebraicClosure ℚ) :=
  DivisionRing.toRatAlgebra

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The exact original arithmetic cyclotomic H2 class has a constructed cyclic cyclotomic unit-H2 representative inside the original unramified extension, with preserved prime torsion and literal original continuous inflation. -/
theorem rationalArithmeticKummerUnitH2_exists_cyclic_stage (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    let U := rationalUnramifiedExtension a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            rationalArithmeticKummerH2Inclusion a q
              (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) := by
  let z : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a) :=
    rationalArithmeticKummerH2Inclusion a q
      (rationalArithmeticCyclotomicH2RootEquiv a q hqa x)
  have h := @originalUnramifiedUnitH2_exists_cyclic_stage (AlgebraicClosure ℚ) _ _
    arithmeticCyclicAmbientAlgebra _ a
    (inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a)))
    (inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a)))
    q (Fact.out : q.Prime) hq2 hqa z (rationalArithmeticKummerUnitH2_nsmul_zero a q hqa x)
  exact h

end
end Dubon2026
