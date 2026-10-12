import Dubon2026.LocalFieldFiniteCyclicReciprocity
import Dubon2026.FiniteGaloisCharacterCarryInflation

/-! # Original finite cyclic local reciprocity commutes with field restriction -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

attribute [local instance] IsCyclic.commGroup

/-- The actual original reciprocity images in a finite cyclic tower
are compatible under the literal restriction of original automorphisms.
This follows by inflating actual character carry cocycles and preserving
their original local invariant. -/
theorem localFieldFiniteCyclicReciprocity_restrict
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    [IsCyclic Gal(E/K)] [IsCyclic Gal(F/K)] (u : Kˣ) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    AlgEquiv.restrictNormalHom E
      (localFieldFiniteCyclicReciprocity K Ω F (Additive.ofMul u)).toMul =
        (localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u)).toMul := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  haveI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
  let χ := galoisUnitGeneratorIndex g hg
  have hi := localFieldFiniteStageInvariant_transition K Ω E F hEF
    (localFieldFiniteCharacterCarryClass K Ω E χ u)
  rw [localFieldFiniteCharacterCarryClass_transition K Ω E F hEF χ u] at hi
  have hE := localFieldFiniteCyclicReciprocity_character K Ω E χ u
  have hF := localFieldFiniteCyclicReciprocity_character K Ω F
    (χ.comp (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))) u
  have heq := (rationalCyclicInvariant_injective (Nat.card Gal(E/K)))
    (hF.symm.trans (hi.trans hE))
  apply (zmodMulEquivOfGenerator hg rfl).symm.injective
  exact Multiplicative.toAdd.injective heq

end
end Dubon2026
