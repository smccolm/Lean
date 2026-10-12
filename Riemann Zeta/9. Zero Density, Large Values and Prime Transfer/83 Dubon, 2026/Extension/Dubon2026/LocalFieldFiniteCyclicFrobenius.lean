import Dubon2026.LocalFieldFiniteCyclicReciprocity
import Dubon2026.LocalFieldContinuousInvariantNormalization
import Dubon2026.LocalFieldCharacterCarryInvariant

/-! # The original local reciprocity map has arithmetic Frobenius normalization -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]

attribute [local instance] IsCyclic.commGroup

/-- On every original unramified extension, the original reciprocity
image of an actual unit is arithmetic Frobenius raised to its original
normalized valuation. Cyclicity is derived from the actual residue extension. -/
theorem localFieldFiniteCyclicReciprocity_frobenius (u : Kˣ) :
    letI : IsCyclic Gal(E/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
    localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u) =
      Additive.ofMul ((localFieldArithmeticFrobenius K E) ^
        localFieldUnitOrder K (Additive.ofMul u)) := by
  haveI : IsCyclic Gal(E/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  haveI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
  let g := localFieldArithmeticFrobenius K E
  have hg := localFieldArithmeticFrobenius_generates K E
  let χ := galoisUnitGeneratorIndex g hg
  have hchar := localFieldFiniteCyclicReciprocity_character K Ω E χ u
  have hperiod := localFieldPeriodRationalInvariant_characterCarry_smul K E χ u
  have hi : localFieldFiniteStageInvariant K Ω E
      (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      localFieldPeriodRationalInvariant K E
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) :=
    localFieldContinuousH2InvariantEquiv_stage K Ω E _
  have hp : rationalCyclicInvariant (Nat.card Gal(E/K))
      (χ (g ^ localFieldUnitOrder K (Additive.ofMul u))).toAdd =
      localFieldUnitOrder K (Additive.ofMul u) •
        rationalCyclicInvariant (Nat.card Gal(E/K)) (χ g).toAdd := by
    rw [map_zpow, toAdd_zpow, map_zsmul]
  have heq := (rationalCyclicInvariant_injective (Nat.card Gal(E/K)))
    ((hchar.symm.trans (hi.trans hperiod)).trans hp.symm)
  apply Additive.toMul.injective
  apply (zmodMulEquivOfGenerator hg rfl).symm.injective
  exact Multiplicative.toAdd.injective heq

end
end Dubon2026
