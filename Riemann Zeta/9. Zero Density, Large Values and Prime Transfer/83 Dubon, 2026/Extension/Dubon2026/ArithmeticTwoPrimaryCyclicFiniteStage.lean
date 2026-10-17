import Dubon2026.OriginalFiniteGaloisImageContainment
import Dubon2026.OriginalTwoPrimaryUnramifiedCyclicStage
import Dubon2026.ArithmeticKummerCyclicCarry

/-! # Two-primary arithmetic descent retains both original finite fields

The existing cyclic totally complex descent is transported through its
literal image in the unchanged arithmetic union. The full cyclotomic
containing field and conductor are retained with the original annihilator
and continuous inflation. These are precisely the inputs for DUB-17's
two-primary principal carry/invariant sum.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra
  SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticGlobalUnitContinuousSMul arithmeticKummerStageAlgebra
  arithmeticKummerStageGalois arithmeticKummerStageTopology arithmeticKummerStageDiscrete
  arithmeticCyclicAmbientAlgebra

variable (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include h2a

/-- The actual two-primary class has a cyclic totally complex finite
stage inside a retained full cyclotomic stage, with the same annihilator
and literal inflation in the original arithmetic union. -/
theorem rationalArithmeticUnitH2_exists_two_primary_cyclic_finite_stage
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      E.toIntermediateField ≤ F.toIntermediateField ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        2 ^ (r + 1) • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y = x := by
  have hs := @originalUnramifiedUnitH2_exists_two_primary_cyclic_subfield
    (AlgebraicClosure ℚ) _ _ arithmeticCyclicAmbientAlgebra _ a
    (inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a)))
    (inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a))) r h2a x hx
  obtain ⟨k, F, hk, hcycl, hF, E, hgal, hcyc, hcomplex, y, hy, hInfl⟩ := hs
  let U := rationalUnramifiedExtension a
  letI : IsGalois ℚ E := hgal
  letI : IsCyclic Gal(E/ℚ) := hcyc
  letI : IsTotallyComplex E := hcomplex
  letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
  letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
  let iE := (IntermediateField.inclusion hF).comp E.val
  letI : Algebra E U := iE.toAlgebra
  letI : SMul E U := iE.toAlgebra.toSMul
  letI : IsScalarTower ℚ E U := IsScalarTower.of_algHom iE
  letI : IsScalarTower E F U := IsScalarTower.of_algebraMap_eq' rfl
  let C := originalFiniteGaloisImage ℚ F U
  let D := originalFiniteGaloisImage ℚ E U
  letI := originalFiniteGaloisImageAlgebra ℚ E U
  letI := originalFiniteGaloisImage_baseTower ℚ E U
  letI := originalFiniteGaloisImage_ambientTower ℚ E U
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ D) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ D) := ⟨rfl⟩
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ E)
    (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := E))
  let z := finiteGaloisUnitBaseChangeH2 ℚ ℚ E D (e.symm y)
  have hz : 2 ^ (r + 1) • z = 0 := by
    have h := congrArg ((finiteGaloisUnitBaseChangeH2 ℚ ℚ E D).comp e.symm.toLinearMap) hy
    simpa only [LinearMap.comp_apply, map_nsmul, map_zero] using h
  letI : IsCyclotomicExtension {2 ^ (k + 1)} ℚ F := hcycl
  refine ⟨k, C, D, hk, IsCyclotomicExtension.equiv {2 ^ (k + 1)} ℚ F
    (originalFiniteGaloisImageEquiv ℚ F U), originalFiniteGaloisImage_le_of_tower ℚ E F U,
    originalFiniteGaloisImage_isCyclic ℚ E U, isTotallyComplex_of_algebra E D, z, hz, ?_⟩
  exact (originalFiniteGaloisImage_inflation ℚ E U (e.symm y)).trans hInfl

end
end Dubon2026
