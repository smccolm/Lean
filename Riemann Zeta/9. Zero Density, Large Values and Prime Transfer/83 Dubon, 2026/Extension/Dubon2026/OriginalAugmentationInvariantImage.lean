import Dubon2026.OriginalAugmentationSubgroupSequence
import Dubon2026.OriginalCoinducedInvariantNorms

/-! # The literal augmentation image on subgroup invariants

Existing coinduced norm preimages and the regular/coinduced isomorphism
show that the augmentation image is exactly the subgroup order times the
integers. This is the kernel calculation for the connecting map that
computes the augmentation ideal's H1 in DUB-17's finite duality argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (S : Subgroup G) [Fintype S]

/-- Every invariant of the actual subgroup-restricted regular coefficient is a literal subgroup norm. -/
theorem originalRegularSubgroupInvariant_norm_preimages :
    ∀ x : Rep.leftRegular ℤ G,
      x ∈ (Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.invariants →
        ∃ y : Rep.leftRegular ℤ G, (Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.norm y = x := by
  let e := (Rep.resFunctor S.subtype).mapIso (originalRegularCoinducedIso (k := ℤ) (G := G))
  exact originalInvariantNorm_preimages_of_retract e.hom e.inv e.hom_inv_id
    (originalCoinducedSubgroupInvariant_norm_preimages (Rep.trivial ℤ G ℤ) S)

omit [Finite G] in
/-- Augmentation of the actual subgroup norm is exactly subgroup order times augmentation. -/
theorem originalAugmentation_subgroup_norm (y : Rep.leftRegular ℤ G) :
    (originalAugmentation ℤ G).hom ((Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.norm y) =
      (Fintype.card S : ℤ) * (originalAugmentation ℤ G).hom y := by
  have he := originalCoefficientMorphism_norm
    ((Rep.resFunctor S.subtype).map (originalAugmentation ℤ G)) y
  change (originalAugmentation ℤ G).hom ((Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.norm y) =
    (Rep.trivial ℤ S ℤ).ρ.norm ((originalAugmentation ℤ G).hom y) at he
  rw [he]
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ _s : S, (originalAugmentation ℤ G).hom y) = _
  rw [Finset.sum_const, Finset.card_univ]
  exact nsmul_eq_mul _ _

/-- The original augmentation image on actual subgroup invariants consists exactly of multiples of the subgroup order. -/
theorem originalAugmentationInvariant_image_iff (z : ℤ) :
    (∃ x : Rep.leftRegular ℤ G,
      x ∈ (Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.invariants ∧
        (originalAugmentation ℤ G).hom x = z) ↔
      ∃ w : ℤ, (Fintype.card S : ℤ) * w = z := by
  constructor
  · rintro ⟨x, hx, haug⟩
    obtain ⟨y, rfl⟩ := originalRegularSubgroupInvariant_norm_preimages S x hx
    exact ⟨(originalAugmentation ℤ G).hom y, (originalAugmentation_subgroup_norm S y).symm.trans haug⟩
  · rintro ⟨w, hw⟩
    let y : Rep.leftRegular ℤ G := Finsupp.single 1 w
    refine ⟨(Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.norm y,
      fun s => Representation.self_norm_apply _ s y, ?_⟩
    rw [originalAugmentation_subgroup_norm]
    have hy : (originalAugmentation ℤ G).hom y = w := by
      rw [originalAugmentation_apply, Finsupp.linearCombination_single]
      exact mul_one w
    rwa [hy]

end
end Dubon2026
