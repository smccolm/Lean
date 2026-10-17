import Dubon2026.OriginalAugmentationGroupChange
import Dubon2026.OriginalFundamentalSplittingSequence

/-! # The literal cocycle correction under group and coefficient change

A one-cochain witnessing compatibility of the two fundamental classes
gives the exact correction on the augmentation ideal. This is the
intertwining identity needed for DUB-17's local/global fundamental norm
comparison and the outside-unit inertia image.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (C : Rep.{0} k G) (D : Rep.{0} k H) (f : G →* H)
  (ℓ : C ⟶ Rep.res f D) (φ : groupCohomology.cocycles₂ C)
  (ψ : groupCohomology.cocycles₂ D) (b : G → D)

/-- A literal cochain correction gives the required augmentation-ideal
identity for the actual two fundamental twists. -/
theorem originalFundamentalTwist_coboundary_comparison
    (hb : ∀ g h : G, ℓ.hom (φ (g, h)) - ψ (f g, f h) =
      D.ρ (f g) (b h) - b (g * h) + b g)
    (g : G) (a : originalAugmentationIdeal k G) :
    ℓ.hom (originalFundamentalCocycleTwist C φ g a.val) +
        Finsupp.linearCombination k b ((originalAugmentationIdeal k G).ρ g a).val =
      originalFundamentalCocycleTwist D ψ (f g)
          ((originalRegularGroupChange (k := k) f).hom a.val) +
        D.ρ (f g) (Finsupp.linearCombination k b a.val) := by
  have hpoint (h : G) : ℓ.hom (φ (g, h)) + b (g * h) =
      ψ (f g, f h) + D.ρ (f g) (b h) + b g := by
    have he := sub_eq_iff_eq_add.mp (hb g h)
    rw [he]
    abel
  have hleft : Finsupp.linearCombination k b
      ((originalAugmentationIdeal k G).ρ g a).val =
        a.val.sum (fun h r => r • b (g * h)) := by
    rw [originalAugmentationIdeal_action, Finsupp.lmapDomain_apply,
      Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    rfl
  have hright : originalFundamentalCocycleTwist D ψ (f g)
      ((originalRegularGroupChange (k := k) f).hom a.val) =
        a.val.sum (fun h r => r • ψ (f g, f h)) := by
    change Finsupp.linearCombination k (fun h => ψ (f g, h))
      (Finsupp.mapDomain f a.val) = _
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    rfl
  rw [hleft, hright, originalFundamentalCocycleTwist_apply,
    Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have he : ∀ h ∈ a.val.support,
      a.val h • ℓ.hom (φ (g, h)) + a.val h • b (g * h) =
        (a.val h • ψ (f g, f h) + a.val h • D.ρ (f g) (b h)) + a.val h • b g := by
    intro h _
    simpa only [smul_add] using congrArg (fun z => a.val h • z) (hpoint h)
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.sum_smul]
  have ha : (∑ h ∈ a.val.support, a.val h) = (0 : k) := by
    have hz := (originalAugmentationIdeal_mem k G a.val).mp a.property
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one] using hz
  rw [ha, zero_smul, add_zero]

end
end Dubon2026
