import Dubon2026.LocalFieldFiniteCyclicCarryInvariant
import Dubon2026.CyclicCharacterInvariantPairing

/-! # The original cyclic norm-residue map evaluates every finite character -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]

attribute [local instance] IsCyclic.commGroup

/-- Every genuine finite character evaluates the original norm-residue
map as the original relative invariant of its actual carry cocycle.
No unramifiedness premise or character-generator assumption is needed. -/
theorem localFieldFiniteCyclicNormResidue_character
    (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldFiniteStageInvariant K Ω E (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      rationalCyclicInvariant n
        (χ (localFieldFiniteCyclicNormResidue K Ω E g hg (Additive.ofMul u)).toMul).toAdd := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [localFieldFiniteCharacterCarryClass_invariant K Ω E g hg]
  let j := localFieldFiniteStageH2CyclicEquiv K Ω E
    ((localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg).symm
      (Submodule.Quotient.mk (Additive.ofMul u)))
  exact (cyclicCharacter_rationalInvariant_pairing g hg
    (IsGalois.card_aut_eq_finrank K E) χ j).symm

/-- The original period-normalized map is independent of the displayed
cyclic generator. The proof uses an actual faithful finite character
and the generator-independent original carry cocycle. -/
theorem localFieldFiniteCyclicNormResidue_generator_independent
    (g h : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hh : ∀ x, x ∈ Subgroup.zpowers h) (u : Additive Kˣ) :
    localFieldFiniteCyclicNormResidue K Ω E g hg u =
      localFieldFiniteCyclicNormResidue K Ω E h hh u := by
  haveI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
  let χ := galoisUnitGeneratorIndex g hg
  have heq := (localFieldFiniteCyclicNormResidue_character K Ω E g hg χ u.toMul).symm.trans
    (localFieldFiniteCyclicNormResidue_character K Ω E h hh χ u.toMul)
  have hchar := (rationalCyclicInvariant_injective (Nat.card Gal(E/K))) heq
  apply Additive.toMul.injective
  apply (zmodMulEquivOfGenerator hg rfl).symm.injective
  exact Multiplicative.toAdd.injective hchar

end
end Dubon2026
