import Dubon2026.ContinuousCoinducedCharacterDualShapiro

/-! # Original induced annihilators from the actual subgroup pairing

Continuous Shapiro, the genuine induced character-dual H1 equivalence and
injectivity of the original scalar corestriction transfer each annihilator.
The subgroup premise will be supplied by split local perfectness and actual
finite splitting-field transport in the DUB-17 local duality argument.
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


/-- A zero left annihilator on the actual subgroup gives a zero left
annihilator on the original induced module, provided its original H2
corestriction is injective. No induced nondegeneracy is assumed. -/
theorem continuousInducedCharacterDualH1Cup_left_zero
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)))
    (x : ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS))
    (hx : ∀ y, continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x y = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := (continuousCoinducedShapiroH1_bijective A S hA hS).surjective x
  have hz : x = 0 := by
    apply hsub
    apply LinearMap.ext
    intro y
    rw [map_zero, LinearMap.zero_apply]
    apply hcor
    exact ((continuousCoinducedCharacterDualShapiro_cup A S χ hχ hA hS x y).symm.trans
      (hx _)).trans (map_zero (continuousRepresentationH2Corestriction
        (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS)).symm
  exact (congrArg (continuousCoinducedShapiroH1 A hA S hS) hz).trans (map_zero _)

/-- The actual subgroup right annihilator transfers through the same
original Shapiro and dual-coefficient equivalences and injective H2 corestriction. -/
theorem continuousInducedCharacterDualH1Cup_right_zero
    (hcor : Function.Injective (continuousRepresentationH2Corestriction
      (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS))
    (hsub : Function.Injective (continuousCharacterDualH1Cup
      (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)).flip)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (Rep.coind S.subtype (Rep.res S.subtype A)) χ)
      (finiteCharacterDualAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A)) χ
        (finiteCoinducedCoefficientAction_continuous A S hA hS) hχ))
    (hy : ∀ x, continuousCharacterDualH1Cup (Rep.coind S.subtype (Rep.res S.subtype A)) χ hχ
      (finiteCoinducedCoefficientAction_continuous A S hA hS) x y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := (continuousCoinducedCharacterDualH1Equiv A S χ hχ hA hS).surjective y
  obtain ⟨y, rfl⟩ := (continuousCoinducedShapiroH1_bijective (characterDualCoefficientRep A χ) S
    (finiteCharacterDualAction_continuous A χ hA hχ) hS).surjective y
  have hz : y = 0 := by
    apply hsub
    apply LinearMap.ext
    intro x
    change continuousCharacterDualH1Cup (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
      (hχ.comp continuous_subtype_val)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x y =
      continuousCharacterDualH1Cup (restrictedCoefficientRep A S.subtype) (χ.comp S.subtype)
        (hχ.comp continuous_subtype_val)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) x 0
    rw [map_zero]
    apply hcor
    exact ((continuousCoinducedCharacterDualShapiro_cup A S χ hχ hA hS x y).symm.trans
      (hy _)).trans (map_zero (continuousRepresentationH2Corestriction
        (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ) S hS)).symm
  rw [hz, map_zero, map_zero]

end
end Dubon2026
