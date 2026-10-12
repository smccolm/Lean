import Dubon2026.ContinuousCoinducedShapiroCochains

/-! # Actual continuous Shapiro maps in degrees one and two

The original cochain lifts preserve actual continuous coboundary witnesses,
so they descend to the existing continuous cohomology quotients. This supplies
one direction of the comparison needed in DUB-17's local duality argument;
inverse identities are a separate obligation.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} R G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Finite (G ⧸ S)] (hS : IsOpen (S : Set G))
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [ContinuousSMul R (Rep.coind S.subtype (Rep.res S.subtype A))]

/-- The original continuous degree-one cocycle lift into actual coinduced coefficients. -/
def continuousCoinducedShapiroCocycleOne :
    continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype) →ₗ[R]
      continuousRepresentationCocyclesOne (Rep.coind S.subtype (Rep.res S.subtype A)) where
  toFun c := ⟨⟨coinducedShapiroOne A S c.val, coinducedShapiroOne_mem_cocycles A S c.val⟩,
    coinducedShapiroOne_continuous A hA S hS c.val c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroOne A S).map_add c.val d.val
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroOne A S).map_smul r c.val

/-- The original jointly continuous degree-two cocycle lift into the same coinduced object. -/
def continuousCoinducedShapiroCocycleTwo :
    continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype) →ₗ[R]
      continuousRepresentationCocyclesTwo (Rep.coind S.subtype (Rep.res S.subtype A)) where
  toFun c := ⟨⟨coinducedShapiroTwo A S c.val, coinducedShapiroTwo_mem_cocycles A S c.val⟩,
    coinducedShapiroTwo_continuous A hA S hS c.val c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroTwo A S).map_add c.val d.val
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroTwo A S).map_smul r c.val

/-- The actual continuous Shapiro map in H1 is induced by the original cocycle
lift; its coboundary witness is the original degree-zero coinduced lift. -/
def continuousCoinducedShapiroH1 :
    ContinuousRepresentationH1 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) →ₗ[R]
    ContinuousRepresentationH1 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) := by
  have hb : continuousRepresentationCoboundariesOne (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≤
      (continuousRepresentationCoboundariesOne (Rep.coind S.subtype (Rep.res S.subtype A))
        (finiteCoinducedCoefficientAction_continuous A S hA hS)).comap
          (continuousCoinducedShapiroCocycleOne A hA S hS) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨coinducedShapiroZero A S a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroOne_coboundary A S a).symm
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype))
    (M₂ := continuousRepresentationCocyclesOne (Rep.coind S.subtype (Rep.res S.subtype A)))
    (τ₁₂ := RingHom.id R) _ _ (continuousCoinducedShapiroCocycleOne A hA S hS) hb

/-- The actual continuous Shapiro map in H2 preserves the original continuous
one-cochain witnesses, using the proved continuous degree-one lift. -/
def continuousCoinducedShapiroH2 :
    ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) →ₗ[R]
    ContinuousRepresentationH2 (Rep.coind S.subtype (Rep.res S.subtype A))
      (finiteCoinducedCoefficientAction_continuous A S hA hS) := by
  have hb : continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≤
      (continuousRepresentationCoboundariesTwo (Rep.coind S.subtype (Rep.res S.subtype A))
        (finiteCoinducedCoefficientAction_continuous A S hA hS)).comap
          (continuousCoinducedShapiroCocycleTwo A hA S hS) := by
    rintro _ ⟨f, rfl⟩
    refine ⟨⟨coinducedShapiroOne A S f,
      coinducedShapiroOne_continuous A hA S hS f f.continuous⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coinducedShapiroTwo_differential A S f).symm
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype))
    (M₂ := continuousRepresentationCocyclesTwo (Rep.coind S.subtype (Rep.res S.subtype A)))
    (τ₁₂ := RingHom.id R) _ _ (continuousCoinducedShapiroCocycleTwo A hA S hS) hb

/-- On original H1 representatives the map is the same continuous coinduced lift. -/
theorem continuousCoinducedShapiroH1_mk
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep A S.subtype)) :
    continuousCoinducedShapiroH1 A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoinducedShapiroCocycleOne A hA S hS c) := rfl

/-- On original H2 representatives the map is the same continuous coinduced lift. -/
theorem continuousCoinducedShapiroH2_mk
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousCoinducedShapiroH2 A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoinducedShapiroCocycleTwo A hA S hS c) := rfl

end
end Dubon2026
