import Dubon2026.OriginalOddPrimaryUnramifiedCyclicStage
import Dubon2026.ArithmeticKummerCyclicCarry

/-! # Actual odd-primary arithmetic unit classes have faithful cyclic carries

The prime-power cyclic descent is specialized to the original rational
arithmetic union. Its literal finite image and the existing cyclic carry
theorem produce a rational-unit carry with identical continuous inflation
and preserved annihilator. This removes the Kummer coefficient restriction
from the representation step in DUB-17's rational reciprocity argument.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete arithmeticCyclicAmbientAlgebra

private theorem arithmeticOddPrimaryFiniteH2_exists_characterCarry
    (a : 𝓞 ℚ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (q k : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    [IsCyclotomicExtension {q ^ (k + 1)} ℚ E] [IsCyclic Gal(E/ℚ)]
    (y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E) :
    letI : Algebra ℚ E := E.toIntermediateField.algebra'
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
    ∃ (n : ℕ) (hn : 1 < n),
      letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
      ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod n), ∃ u : ℚˣ,
        Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = y := by
  letI : Algebra ℚ E := E.toIntermediateField.algebra'
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  have hn := oddPrimeCyclotomic_galois_card_gt_one E q k hq hq2
  letI : NeZero (Nat.card Gal(E/ℚ)) := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  have h := originalCyclicContinuousH2_exists_characterCarry ℚ E hn y
  obtain ⟨χ, u, hu⟩ := h
  exact ⟨Nat.card Gal(E/ℚ), hn, χ, u, hu⟩

variable (a : 𝓞 ℚ) (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

include hq hq2 hqa

/-- The original arithmetic unit class has a cyclic stage with its full prime-power annihilator. -/
theorem rationalArithmeticUnitH2_exists_odd_primary_cyclic_stage
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    let U := rationalUnramifiedExtension a
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)),
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      ∃ hF : F.toIntermediateField ≤ U,
        letI : Algebra F U := (IntermediateField.inclusion hF).toAlgebra
        letI : IsScalarTower ℚ F U := IsScalarTower.of_algHom (IntermediateField.inclusion hF)
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
        ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ F) 2, q ^ (r + 1) • y = 0 ∧
          continuousGaloisUnitBaseChangeH2 ℚ ℚ F U
            ((continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits ℚ F)
              (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := F))).symm y) =
            x := by
  exact @originalUnramifiedUnitH2_exists_odd_primary_cyclic_stage (AlgebraicClosure ℚ) _ _
    arithmeticCyclicAmbientAlgebra _ a
    (inferInstanceAs (TopologicalSpace (rationalArithmeticUnitRepresentation a)))
    (inferInstanceAs (DiscreteTopology (rationalArithmeticUnitRepresentation a)))
    q r hq hq2 hqa x hx

/-- The actual unit class is inflated from the literal finite image of the constructed cyclic stage. -/
theorem rationalArithmeticUnitH2_exists_odd_primary_cyclic_finite_stage
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q ^ (r + 1) • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y =
          x := by
  have hstage := rationalArithmeticUnitH2_exists_odd_primary_cyclic_stage a q r hq hq2 hqa x hx
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
  have hz : q ^ (r + 1) • z = 0 := by
    have h := congrArg ((finiteGaloisUnitBaseChangeH2 ℚ ℚ F E).comp e.symm.toLinearMap) hqy
    simpa only [LinearMap.comp_apply, map_nsmul, map_zero] using h
  refine ⟨k, E, hk, IsCyclotomicExtension.equiv {q ^ (k + 1)} ℚ F
    (originalFiniteGaloisImageEquiv ℚ F U), originalFiniteGaloisImage_isCyclic ℚ F U, z, hz, ?_⟩
  exact (originalFiniteGaloisImage_inflation ℚ F U (e.symm y)).trans hy


/-- A faithful rational-unit cyclic carry represents the same actual odd-primary arithmetic class. -/
theorem rationalArithmeticUnitH2_exists_odd_primary_cyclic_carry
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : q ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      letI : Algebra ℚ E := E.toIntermediateField.algebra'
      r + 1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q ^ (r + 1) • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y = x ∧
        ∃ (n : ℕ) (hn : 1 < n),
          letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
          ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod n), ∃ u : ℚˣ,
            Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = y := by
  have hstage := rationalArithmeticUnitH2_exists_odd_primary_cyclic_finite_stage a q r hq hq2 hqa x hx
  obtain ⟨k, E, hk, hcycl, hcyc, y, hyq, hy⟩ := hstage
  letI : Algebra ℚ E := E.toIntermediateField.algebra'
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ E := hcycl
  letI : IsCyclic Gal(E/ℚ) := hcyc
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  have hc := arithmeticOddPrimaryFiniteH2_exists_characterCarry a E q k hq hq2 y
  exact ⟨k, E, hk, hcycl, hcyc, y, hyq, hy, hc⟩

end
end Dubon2026
