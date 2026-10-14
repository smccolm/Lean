import Dubon2026.ArithmeticKummerCyclicH2Stage
import Dubon2026.OriginalFiniteGaloisImageInflation

/-! # The actual arithmetic Kummer class has a cyclic finite stage in its original union

The constructed cyclotomic stage is identified with its literal finite
image inside the original unramified extension. The already proved image
inflation identity preserves the class, while the actual linear maps
preserve its prime torsion. This is the source entry into the original
arithmetic finite-local carry pairing for DUB-17's invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete arithmeticCyclicAmbientAlgebra

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The exact arithmetic Kummer class is the original finite inflation of a prime-torsion class on a constructed cyclic cyclotomic finite stage of the same original unramified union. -/
theorem rationalArithmeticKummerUnitH2_exists_cyclic_finite_stage (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) := by
  have hstage := rationalArithmeticKummerUnitH2_exists_cyclic_stage a q hqa hq2 x
  obtain ⟨k, F, hk, hcycl, hcyc, hF, y, hqy, hy⟩ := hstage
  let U := rationalUnramifiedExtension a
  letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
  letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
  letI : IsCyclic Gal(F/ℚ) := hcyc
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcycl
  let E := originalFiniteGaloisImage ℚ F U
  letI := originalFiniteGaloisImageAlgebra ℚ F U
  letI := originalFiniteGaloisImage_baseTower ℚ F U
  letI := originalFiniteGaloisImage_ambientTower ℚ F U
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
    (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))
  let z := finiteGaloisUnitBaseChangeH2 ℚ ℚ F E (e.symm y)
  have hz : q • z = 0 := by
    have h := congrArg ((finiteGaloisUnitBaseChangeH2 ℚ ℚ F E).comp e.symm.toLinearMap) hqy
    simpa only [LinearMap.comp_apply, map_nsmul, map_zero] using h
  refine ⟨k, E, hk, IsCyclotomicExtension.equiv {q ^ (k + 1)} ℚ F
    (originalFiniteGaloisImageEquiv ℚ F U), originalFiniteGaloisImage_isCyclic ℚ F U, z, hz, ?_⟩
  exact (originalFiniteGaloisImage_inflation ℚ F U (e.symm y)).trans hy

end
end Dubon2026
