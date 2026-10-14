import Dubon2026.OriginalCyclicGaloisH2CarryRepresentatives
import Dubon2026.GaloisUnitCharacterCarryPeriod
import Dubon2026.ContinuousDiscreteH2Comparison
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Original continuous cyclic H2 classes have literal carry representatives

The faithful cyclic character is constructed from the actual Galois group.
The already proved algebraic carry theorem and same-cocycle comparison
give its continuous representative. This removes the carry-representative
premise from the arithmetic finite-stage local pairing on DUB-17's route.
-/
namespace Dubon2026
noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

/-- A nontrivial actual finite cyclic Galois H2 class has a constructed faithful character and a literal continuous carry representative from an original base-field unit. -/
theorem originalCyclicContinuousH2_exists_characterCarry
    (hn : 1 < Nat.card Gal(L/K)) (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    let n := Nat.card Gal(L/K)
    letI : NeZero n := ⟨by omega⟩
    ∃ χ : Gal(L/K) ≃* Multiplicative (ZMod n), ∃ u : Kˣ,
      Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ.toMonoidHom u) = x := by
  let n := Nat.card Gal(L/K)
  letI : NeZero n := ⟨by omega⟩
  let χ : Gal(L/K) ≃* Multiplicative (ZMod n) := (zmodCyclicMulEquiv inferInstance).symm
  let e := continuousDiscreteH2Equiv (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
  obtain ⟨u, hu⟩ := originalCyclicGaloisH2_exists_characterCarry K L χ hn (e x)
  refine ⟨χ, u, e.injective ?_⟩
  exact hu

end
end Dubon2026
