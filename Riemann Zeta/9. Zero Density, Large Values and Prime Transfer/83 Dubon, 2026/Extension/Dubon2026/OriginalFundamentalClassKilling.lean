import Dubon2026.OriginalFundamentalSplittingSequence

/-! # The literal extension kills its original two-cocycle class

The cochain is constructed from the original cocycle and the actual
augmentation differences. This discharges the class-killing input of the
finite splitting-coefficient vanishing argument on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]

/-- The actual augmentation difference associated to a group element. -/
def originalAugmentationDifference (g : G) : originalAugmentationIdeal k G :=
  ⟨Finsupp.single g 1 - Finsupp.single 1 1, by
    rw [originalAugmentationIdeal_mem, map_sub, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, sub_self]⟩

/-- The augmentation differences satisfy their literal one-cocycle identity. -/
theorem originalAugmentationDifference_cocycle (g h : G) :
    (originalAugmentationIdeal k G).ρ g (originalAugmentationDifference h) -
        originalAugmentationDifference (g * h) + originalAugmentationDifference g = 0 := by
  apply Subtype.ext
  change Finsupp.lmapDomain k k (g * ·) (Finsupp.single h 1 - Finsupp.single 1 1) -
    (Finsupp.single (g * h) 1 - Finsupp.single 1 1) +
      (Finsupp.single g 1 - Finsupp.single 1 1) = 0
  rw [map_sub, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, mul_one]
  abel

variable (C : Rep k G) (φ : groupCohomology.cocycles₂ C)

/-- The cocycle identity compares the original right-identity values under translation. -/
theorem originalFundamentalCocycle_one_right_action (g h : G) :
    C.ρ g (φ (h, 1)) = φ (g * h, 1) := by
  have hx := (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2 g h 1
  rw [mul_one] at hx
  exact add_right_cancel hx.symm

/-- The actual splitting inclusion kills exactly the cohomology class of its defining cocycle. -/
theorem originalFundamentalSplittingInclusion_class_zero :
    (groupCohomology.map (MonoidHom.id G) (originalFundamentalSplittingInclusion C φ) 2)
      (groupCohomology.H2π C φ) = 0 := by
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_eq_zero_iff,
    groupCohomology.coe_mapCocycles₂]
  refine ⟨fun g => (φ (g, 1), originalAugmentationDifference g), funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  refine Prod.ext ?_ ?_
  · change C.ρ g (φ (h, 1)) +
        originalFundamentalCocycleTwist C φ g (Finsupp.single h 1 - Finsupp.single 1 1) -
          φ (g * h, 1) + φ (g, 1) = φ (g, h)
    rw [map_sub, originalFundamentalCocycleTwist_single,
      originalFundamentalCocycleTwist_single, one_smul, one_smul,
      originalFundamentalCocycle_one_right_action]
    abel
  · exact originalAugmentationDifference_cocycle g h

end
end Dubon2026
