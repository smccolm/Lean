import Dubon2026.ArithmeticTwoPrimaryCyclicFiniteStage

/-! # The original two-primary class has a faithful cyclic carry

The constructed totally complex stage has even positive degree, hence
nontrivial cyclic Galois group. The existing same-cocycle carry theorem
then supplies an actual rational unit while retaining the full containing
field, annihilator and inflation needed for DUB-17's invariant sum.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical

/-- A totally complex finite rational Galois extension has nontrivial
Galois group, as its positive degree is even. -/
theorem totallyComplexGalois_card_gt_one
    (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [IsTotallyComplex L] : 1 < Nat.card Gal(L/ℚ) := by
  letI : NumberField L := NumberField.of_module_finite ℚ L
  rw [IsGalois.card_aut_eq_finrank]
  have he : Module.finrank ℚ L = 2 * InfinitePlace.nrComplexPlaces L := by
    convert IsTotallyComplex.finrank L using 1
    exact congrArg (fun m : Module ℚ L => @Module.finrank ℚ L _ _ m) (Subsingleton.elim _ _)
  have hp : 0 < Module.finrank ℚ L := Module.finrank_pos
  omega

attribute [-instance] UniformSpace.Completion.instSMul DivisionRing.toRatAlgebra
  SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticGlobalUnitContinuousSMul arithmeticKummerStageAlgebra
  arithmeticKummerStageGalois arithmeticKummerStageTopology arithmeticKummerStageDiscrete

variable (a : 𝓞 ℚ) (r : ℕ) (h2a : (2 : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
include h2a

omit h2a [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)] in
private theorem arithmeticTwoPrimaryFiniteH2_carry
    (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(E/ℚ)] [IsTotallyComplex E]
    (y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E) :
    letI : Algebra ℚ E := E.toIntermediateField.algebra'
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
    ∃ (d : ℕ) (hd : 1 < d),
      letI : NeZero d := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)⟩
      ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod d), ∃ q : ℚˣ,
        Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom q) = y := by
  letI : Algebra ℚ E := E.toIntermediateField.algebra'
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
  have hd := totallyComplexGalois_card_gt_one E
  have hc := originalCyclicContinuousH2_exists_characterCarry ℚ E hd y
  exact ⟨Nat.card Gal(E/ℚ), hd, hc⟩

/-- A faithful rational-unit carry represents the same actual two-primary
class, inside the retained full cyclotomic field with the same conductor
and prime-power annihilator. -/
theorem rationalArithmeticUnitH2_exists_two_primary_cyclic_carry
    (x : GaloisUnitContinuousH2 (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (hx : 2 ^ (r + 1) • x = 0) :
    ∃ (k : ℕ) (F E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)),
      letI : Algebra ℚ E := E.toIntermediateField.algebra'
      r + 2 ≤ k ∧ IsCyclotomicExtension {2 ^ (k + 1)} ℚ F ∧
      E.toIntermediateField ≤ F.toIntermediateField ∧ IsCyclic Gal(E/ℚ) ∧ IsTotallyComplex E ∧
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
      ∃ y : GaloisUnitH2FiniteStage ℚ (rationalUnramifiedExtension a) E,
        2 ^ (r + 1) • y = 0 ∧ galoisUnitFiniteStageH2Inflation E y = x ∧
        ∃ (d : ℕ) (hd : 1 < d),
          letI : NeZero d := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)⟩
          ∃ χ : Gal(E/ℚ) ≃* Multiplicative (ZMod d), ∃ q : ℚˣ,
            Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom q) = y :=
  Exists.imp (fun _ => Exists.imp (fun _ => Exists.imp (fun E hs =>
    letI : Algebra ℚ E := E.toIntermediateField.algebra'
    letI : IsCyclic Gal(E/ℚ) := hs.2.2.2.1
    letI : IsTotallyComplex E := hs.2.2.2.2.1
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ E) := ⟨rfl⟩
    And.intro hs.1 (And.intro hs.2.1 (And.intro hs.2.2.1
      (And.intro hs.2.2.2.1 (And.intro hs.2.2.2.2.1
        (Exists.imp (fun y hy => And.intro hy.1
          (And.intro hy.2 (arithmeticTwoPrimaryFiniteH2_carry a E y))) hs.2.2.2.2.2))))))))
    (rationalArithmeticUnitH2_exists_two_primary_cyclic_finite_stage a r h2a x hx)

end
end Dubon2026
