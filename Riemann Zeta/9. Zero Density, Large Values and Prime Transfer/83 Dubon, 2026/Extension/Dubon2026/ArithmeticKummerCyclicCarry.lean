import Dubon2026.ArithmeticKummerCyclicFiniteStage
import Dubon2026.OddPrimeCyclotomicGaloisNontrivial

/-! # The original arithmetic Kummer class has a constructed finite cyclic carry

The original class enters the proved finite cyclotomic stage, whose
nontriviality and faithful character are derived. The resulting actual
rational-unit carry has the original prime torsion and literally inflates
to that Kummer class. This is the source entry for DUB-17's arithmetic
local pairing; the cyclotomic principal product remains to be proved.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra SubfieldClass.instSMulRat
attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  arithmeticKummerStageAlgebra arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete arithmeticCyclicAmbientAlgebra

private theorem arithmeticCyclicFiniteH2_exists_characterCarry
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

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The actual odd-prime arithmetic Kummer class is represented by a constructed faithful cyclic carry from a rational unit, with its torsion and original finite inflation preserved. -/
theorem rationalArithmeticKummerUnitH2_exists_cyclic_carry (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    ∃ (k : ℕ) (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      letI : Algebra ℚ E := E.toIntermediateField.algebra'
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ E ∧ IsCyclic Gal(E/ℚ) ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        q • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y =
          rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) ∧
        ∃ (n : ℕ) (hn : 1 < n),
          letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
          ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod n), ∃ u : ℚˣ,
            Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = y := by
  have hstage := rationalArithmeticKummerUnitH2_exists_cyclic_finite_stage a q hqa hq2 x
  obtain ⟨k, E, hk, hcycl, hcyc, y, hqy, hy⟩ := hstage
  letI : Algebra ℚ E := E.toIntermediateField.algebra'
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ E := hcycl
  letI : IsCyclic Gal(E/ℚ) := hcyc
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  have hc := arithmeticCyclicFiniteH2_exists_characterCarry a E q k (Fact.out : q.Prime) hq2 y
  exact ⟨k, E, hk, hcycl, hcyc, y, hqy, hy, hc⟩

end
end Dubon2026
