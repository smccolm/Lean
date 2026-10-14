import Dubon2026.LocalFieldCarryNormInvariant
import Dubon2026.FiniteCharacterBaseRestrictionInflation
import Dubon2026.LocalFieldFiniteCyclicReciprocity

/-! # Original finite cyclic local reciprocity commutes with field norms

The original maps are compared through an actual faithful finite character.
The proved norm/corestriction formula preserves their normalized invariants,
and genuine finite character inflation supplies both original finite-stage
consumers. This removes the norm-compatibility premise from the ramified
cyclotomic reciprocity route serving DUB-17's arithmetic invariant sum.
-/
namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [IsCyclic Gal(L/K)] [IsCyclic Gal(M/E)]
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]

attribute [local instance] IsCyclic.commGroup

omit [IsCyclic Gal(L/K)] [IsCyclic Gal(M/E)] in
/-- Both original finite carry invariants are compared through their actual continuous inflations. -/
private theorem localFieldFiniteCarryInvariant_norm
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Eˣ) :
    localFieldFiniteStageInvariant K Ω L
      (localFieldFiniteCharacterCarryClass K Ω L χ (Units.map (Algebra.norm K (S := E)) u)) =
      localFieldFiniteStageInvariant E Ω M
        (localFieldFiniteCharacterCarryClass E Ω M
          (χ.comp (galoisBaseChangeRestriction K E L M)) u) := by
  have hi := localFieldContinuousCarryInvariant_norm K Ω E
    (finiteGaloisCharacterInflation L χ) u
  rw [finiteGaloisCharacterInflation_baseRestriction K Ω E L M χ,
    ← continuousFiniteCharacterCarryClass_inflation,
    ← continuousFiniteCharacterCarryClass_inflation] at hi
  change localFieldFiniteStageInvariant K Ω L
    (localFieldFiniteCharacterCarryClass K Ω L χ (Units.map (Algebra.norm K (S := E)) u)) =
      localFieldFiniteStageInvariant E Ω M
        (localFieldFiniteCharacterCarryClass E Ω M
          (χ.comp (galoisBaseChangeRestriction K E L M)) u) at hi
  exact hi

/-- Actual field norm on original units corresponds to literal restriction of the original finite cyclic local reciprocity maps. -/
theorem localFieldFiniteCyclicReciprocity_norm (u : Eˣ) :
    galoisBaseChangeRestriction K E L M
      (localFieldFiniteCyclicReciprocity E Ω M (Additive.ofMul u)).toMul =
      (localFieldFiniteCyclicReciprocity K Ω L
        (Additive.ofMul (Units.map (Algebra.norm K (S := E)) u))).toMul := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  haveI : NeZero (Nat.card Gal(L/K)) := ⟨Nat.card_pos.ne'⟩
  let χ := galoisUnitGeneratorIndex g hg
  have hi := localFieldFiniteCarryInvariant_norm K Ω E L M χ u
  have hK := localFieldFiniteCyclicReciprocity_character K Ω L χ
    (Units.map (Algebra.norm K (S := E)) u)
  have hE := localFieldFiniteCyclicReciprocity_character E Ω M
    (χ.comp (galoisBaseChangeRestriction K E L M)) u
  have heq := (rationalCyclicInvariant_injective (Nat.card Gal(L/K)))
    (hE.symm.trans (hi.symm.trans hK))
  apply (zmodMulEquivOfGenerator hg rfl).symm.injective
  exact Multiplicative.toAdd.injective heq

end
end Dubon2026
