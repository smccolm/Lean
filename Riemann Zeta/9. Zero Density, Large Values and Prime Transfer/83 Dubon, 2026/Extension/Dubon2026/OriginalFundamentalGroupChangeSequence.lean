import Dubon2026.OriginalFundamentalTwistComparison
import Dubon2026.OriginalFundamentalClassCochainComparison

/-! # An actual map of fundamental extensions under group change

The explicit cochain correction builds a morphism of the literal
fundamental sequences, preserving the coefficient and augmentation maps.
The existing H2 compatibility supplies that correction. This is needed
to identify local-unit images with inertia on DUB-17's norm-field route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (C : Rep.{0} k G) (D : Rep.{0} k H) (f : G →* H)
  (ℓ : C ⟶ Rep.res f D) (φ : groupCohomology.cocycles₂ C)
  (ψ : groupCohomology.cocycles₂ D) (b : G → D)
  (hb : ∀ g h : G, ℓ.hom (φ (g, h)) - ψ (f g, f h) =
    D.ρ (f g) (b h) - b (g * h) + b g)

/-- The literal coefficient map and cochain correction define an actual
morphism of the twisted fundamental middle representations. -/
def originalFundamentalGroupChangeMiddle :
    originalFundamentalSplittingModule C φ ⟶
      Rep.res f (originalFundamentalSplittingModule D ψ) :=
  Rep.ofHom {
    toLinearMap := LinearMap.prod
      (ℓ.hom.toLinearMap.comp (LinearMap.fst k C (originalAugmentationIdeal k G)) +
        (Finsupp.linearCombination k b).comp
          ((LinearMap.ker (originalAugmentation k G).hom.toLinearMap).subtype.comp
            (LinearMap.snd k C (originalAugmentationIdeal k G))))
      ((originalAugmentationGroupChange (k := k) f).hom.toLinearMap.comp
        (LinearMap.snd k C (originalAugmentationIdeal k G)))
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · change ℓ.hom (C.ρ g v.1 + originalFundamentalCocycleTwist C φ g v.2.val) +
          Finsupp.linearCombination k b ((originalAugmentationIdeal k G).ρ g v.2).val =
            D.ρ (f g) (ℓ.hom v.1 + Finsupp.linearCombination k b v.2.val) +
              originalFundamentalCocycleTwist D ψ (f g)
                ((originalRegularGroupChange (k := k) f).hom v.2.val)
        have hc := Rep.hom_comm_apply ℓ g v.1
        change ℓ.hom (C.ρ g v.1) = D.ρ (f g) (ℓ.hom v.1) at hc
        rw [map_add, hc, map_add, add_assoc,
          originalFundamentalTwist_coboundary_comparison C D f ℓ φ ψ b hb]
        abel
      · exact Rep.hom_comm_apply (originalAugmentationGroupChange (k := k) f) g v.2 }

/-- The explicit corrected middle map forms the actual group-change
diagram between the original fundamental coefficient sequences. -/
def originalFundamentalGroupChangeSequenceMap :
    originalFundamentalSplittingShortComplex C φ ⟶
      (originalFundamentalSplittingShortComplex D ψ).map (Rep.resFunctor f) where
  τ₁ := ℓ
  τ₂ := originalFundamentalGroupChangeMiddle C D f ℓ φ ψ b hb
  τ₃ := originalAugmentationGroupChange f
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    apply Prod.ext
    · change ℓ.hom c = ℓ.hom c + Finsupp.linearCombination k b 0
      rw [map_zero, add_zero]
    · exact (map_zero (originalAugmentationGroupChange (k := k) f).hom).symm
  comm₂₃ := rfl

/-- Compatibility of the actual H2 classes constructs a corrected
fundamental sequence map with the prescribed coefficient and augmentation legs. -/
theorem originalFundamentalGroupChangeSequenceMap_exists
    (hclass : groupCohomology.map (MonoidHom.id G) ℓ 2 (groupCohomology.H2π C φ) =
      groupCohomology.map f (𝟙 (Rep.res f D)) 2 (groupCohomology.H2π D ψ)) :
    ∃ m : originalFundamentalSplittingShortComplex C φ ⟶
        (originalFundamentalSplittingShortComplex D ψ).map (Rep.resFunctor f),
      m.τ₁ = ℓ ∧ m.τ₃ = originalAugmentationGroupChange f := by
  obtain ⟨b, hb⟩ := originalFundamentalClass_exists_cochain_comparison C D f ℓ φ ψ hclass
  exact ⟨originalFundamentalGroupChangeSequenceMap C D f ℓ φ ψ b hb, rfl, rfl⟩

end
end Dubon2026
