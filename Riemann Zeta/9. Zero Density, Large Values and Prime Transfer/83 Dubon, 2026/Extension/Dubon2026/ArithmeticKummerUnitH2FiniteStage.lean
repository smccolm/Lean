import Dubon2026.ArithmeticFiniteInvariantSumComparison
import Dubon2026.ContinuousGaloisH2TorsionFiniteStage

/-! # The actual arithmetic Kummer class has a torsion-preserving finite unit stage

The same arithmetic class used in the invariant sum is sent through its
original root equivalence and Kummer inclusion. Its coefficient prime
annihilates it. Actual finite descent and injective inflation preserve that
annihilator in a constructed finite stage of the original unramified union.
This supplies the source entry for DUB-17's proved cyclic descent theorem.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
attribute [-instance] DivisionRing.toRatAlgebra SubfieldClass.instSMulRat

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- Retain the native original arithmetic extension's rational algebra. -/
local instance arithmeticKummerStageAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- Use the proved original arithmetic Galois structure. -/
local instance arithmeticKummerStageGalois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a

/-- Use the same original arithmetic coefficient topology. -/
local instance arithmeticKummerStageTopology :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
  inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a))

/-- Retain discreteness of the same original coefficient topology. -/
local instance arithmeticKummerStageDiscrete :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) :=
  inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a))

/-- The exact original arithmetic Kummer image is annihilated by its coefficient prime. -/
theorem rationalArithmeticKummerUnitH2_nsmul_zero
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    q • rationalArithmeticKummerH2Inclusion a q
      (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) = 0 := by
  have hx : q • x = 0 := by
    have h := zero_smul (ZMod q) x
    simpa only [← ZMod.natCast_self q, Nat.cast_smul_eq_nsmul] using h
  rw [← map_nsmul, ← map_nsmul, hx, map_zero, map_zero]

/-- The same arithmetic class in the invariant sum has an actual finite unit-H2 presentation inside the original arithmetic extension, with its prime annihilator derived and preserved. -/
theorem rationalArithmeticKummerUnitH2_exists_torsion_finite_stage
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
      ∃ y : GaloisUnitContinuousH2 (K := ℚ) (Ω := F), q • y = 0 ∧
        galoisUnitFiniteStageH2Inflation (K := ℚ) (Ω := rationalUnramifiedExtension a) F y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  let z : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a) :=
    rationalArithmeticKummerH2Inclusion a q
    (rationalArithmeticCyclotomicH2RootEquiv a q hqa x)
  exact continuousGaloisUnitH2_exists_torsion_finite_stage q z
    (rationalArithmeticKummerUnitH2_nsmul_zero a q hqa x)

end
end Dubon2026
