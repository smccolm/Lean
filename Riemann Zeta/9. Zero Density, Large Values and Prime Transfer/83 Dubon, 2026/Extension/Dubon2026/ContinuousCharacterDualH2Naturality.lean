import Dubon2026.ContinuousCharacterDualH2Pairing

/-! # Naturality of the original H2/H0 pairing

Actual invariant restriction and original dual precomposition commute with
the original endpoint evaluation. This lets a proved induced endpoint
realize arbitrary functionals on the original invariant space, as needed
for the direct DUB-17 local H1 annihilator argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  (A B : Rep.{0} k G) (φ : A →ₗ[k] B)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))

/-- Restrict the original equivariant coefficient map to its actual invariants. -/
def coefficientInvariantLinearMap : A.ρ.invariants →ₗ[k] B.ρ.invariants where
  toFun w := ⟨φ w.val, fun g => (hφρ g w.val).symm.trans (congrArg φ (w.property g))⟩
  map_add' _ _ := Subtype.ext (map_add φ _ _)
  map_smul' _ _ := Subtype.ext (map_smul φ _ _)

/-- An original coefficient inclusion remains injective on its actual invariants. -/
theorem coefficientInvariantLinearMap_injective (hφ : Function.Injective φ) :
    Function.Injective (coefficientInvariantLinearMap A B φ hφρ) := by
  intro u v h
  exact Subtype.ext (hφ (congrArg Subtype.val h))

variable
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep B χ)]
  [DiscreteTopology (characterDualCoefficientRep B χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The actual coefficient H2 map and actual invariant map are adjoint for
the original character-dual endpoint, by literal evaluation on original cocycles. -/
theorem continuousCharacterDualH2InvariantPairing_naturality
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep B χ)
      (finiteCharacterDualAction_continuous B χ hB hχ)) (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA
      (continuousCoefficientH2Map (characterDualCoefficientRep B χ) (characterDualCoefficientRep A χ)
        (characterDualCoefficientMap A B χ φ) continuous_of_discreteTopology
        (characterDualCoefficientMap_equivariant A B χ φ hφρ)
        (finiteCharacterDualAction_continuous B χ hB hχ)
        (finiteCharacterDualAction_continuous A χ hA hχ) x) w =
      continuousCharacterDualH2InvariantPairing B χ hχ hB x
        (coefficientInvariantLinearMap A B φ hφρ w) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
