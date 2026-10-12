import Dubon2026.LocalFieldFiniteCyclicCharacterPairing

/-! # The original finite cyclic local reciprocity homomorphism -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]

attribute [local instance] IsCyclic.commGroup

/-- The actual original finite cyclic local reciprocity map.
Its construction uses the normalized fundamental class and actual
cocycle period. The preceding character theorem proves independence
of the generator used to construct it. -/
def localFieldFiniteCyclicReciprocity : Additive Kˣ →+ Additive Gal(E/K) :=
  localFieldFiniteCyclicNormResidue K Ω E
    (IsCyclic.exists_generator (α := Gal(E/K))).choose
    (IsCyclic.exists_generator (α := Gal(E/K))).choose_spec

/-- Any generator computes the same original reciprocity map. -/
theorem localFieldFiniteCyclicReciprocity_eq_normResidue
    (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g) (u : Additive Kˣ) :
    localFieldFiniteCyclicReciprocity K Ω E u =
      localFieldFiniteCyclicNormResidue K Ω E g hg u :=
  localFieldFiniteCyclicNormResidue_generator_independent K Ω E _ g _ hg u

/-- The original finite cyclic reciprocity map is onto the actual Galois group. -/
theorem localFieldFiniteCyclicReciprocity_surjective :
    Function.Surjective (localFieldFiniteCyclicReciprocity K Ω E) :=
  localFieldFiniteCyclicNormResidue_surjective K Ω E _ _

/-- Its kernel is precisely the actual norms of original extension-field units. -/
theorem localFieldFiniteCyclicReciprocity_eq_zero_iff (u : Additive Kˣ) :
    localFieldFiniteCyclicReciprocity K Ω E u = 0 ↔
      ∃ v : Eˣ, Units.map (Algebra.norm K (S := E)) v = u.toMul :=
  localFieldFiniteCyclicNormResidue_eq_zero_iff K Ω E _ _ u

/-- The character pairing identifies the canonical original reciprocity
map with the invariant of each actual original character carry cocycle. -/
theorem localFieldFiniteCyclicReciprocity_character
    {n : ℕ} [NeZero n] (χ : Gal(E/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldFiniteStageInvariant K Ω E (localFieldFiniteCharacterCarryClass K Ω E χ u) =
      rationalCyclicInvariant n
        (χ (localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u)).toMul).toAdd :=
  localFieldFiniteCyclicNormResidue_character K Ω E _ _ χ u

end
end Dubon2026
