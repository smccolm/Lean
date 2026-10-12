import Dubon2026.ContinuousCoinducedShapiroH2Invariant

/-! # Transfer of the original induced H2/H0 annihilators

Actual continuous H2 Shapiro, the original dual equivalence and the invariant
identification transfer the subgroup endpoint through injective scalar H2
corestriction. These narrower inputs are supplied by local splitting-field
results in DUB-17's finite-module local-duality dependency chain.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul coinducedCoefficient_finite
  coinducedDualShapiroScalarContinuous coinducedDualShapiroDualScalarContinuous

variable {k G : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (S : Subgroup G) [Fintype (G ⧸ S)] (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype (characterDualCoefficientRep A χ)))]
  [TopologicalSpace (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G))


/-- The actual subgroup endpoint detects induced dual H2 classes through
original Shapiro and original injective scalar corestriction. -/
theorem continuousInducedCharacterDualH2InvariantPairing_left_zero
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)))
    (x : ContinuousRepresentationH2
      (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
      (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
        (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ))
    (hx : ∀ w, continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x w = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := (continuousCoinducedCharacterDualH2Equiv A S χ hχ hA hS).surjective x
  obtain ⟨x, rfl⟩ := (continuousCoinducedShapiroH2_bijective (characterDualCoefficientRep A χ) S
    (finiteCharacterDualAction_continuous A χ hA hχ) hS).surjective x
  have hz : x = 0 := by
    apply hsub
    apply LinearMap.ext
    intro w
    have heq : continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
        (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x w = 0 := by
      apply hcor
      exact ((continuousCoinducedShapiroH2Invariant_pairing A S χ hχ hA hS x w).symm.trans
        (hx _)).trans (map_zero (continuousRepresentationH2Corestriction
          (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS)).symm
    exact heq.trans (DFunLike.congr_fun (map_zero (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))) w).symm
  rw [hz, map_zero, map_zero]

/-- The actual subgroup endpoint detects induced invariants through the
same original H2 comparison and genuine invariant-space equivalence. -/
theorem continuousInducedCharacterDualH2InvariantPairing_right_zero
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH2InvariantPairing
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (w : (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants)
    (hw : ∀ x, continuousCharacterDualH2InvariantPairing (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x w = 0) : w = 0 := by
  obtain ⟨w, rfl⟩ := (coinducedInvariantEquiv A S).surjective w
  have hz : w = 0 := by
    apply hsub
    apply LinearMap.ext
    intro x
    change continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
      (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x w =
      continuousCharacterDualH2InvariantPairing (restrictedCoefficientRep A S.subtype)
        (χ.comp S.subtype) (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x 0
    rw [map_zero]
    apply hcor
    exact ((continuousCoinducedShapiroH2Invariant_pairing A S χ hχ hA hS x w).symm.trans
      (hw _)).trans (map_zero (continuousRepresentationH2Corestriction
        (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS)).symm
  exact (congrArg (coinducedInvariantEquiv A S) hz).trans (map_zero _)

end
end Dubon2026
