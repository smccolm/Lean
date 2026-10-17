import Dubon2026.OriginalAugmentationSequence

/-! # The actual augmentation sequence under group change

The literal group-ring map sends the original augmentation ideal to the
target ideal. This is the coefficient diagram needed to compare local
and global fundamental norm maps and identify the outside-unit inertia
image in DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H] (f : G →* H)

/-- The literal group-ring map associated with the actual group map. -/
def originalRegularGroupChange : Rep.leftRegular k G ⟶ Rep.res f (Rep.leftRegular k H) :=
  Rep.ofHom {
    toLinearMap := Finsupp.lmapDomain k k f
    isIntertwining' g := by
      apply Finsupp.lhom_ext
      intro h a
      change Finsupp.lmapDomain k k f
        (Finsupp.lmapDomain k k (g * ·) (Finsupp.single h a)) =
        Finsupp.lmapDomain k k (f g * ·)
          (Finsupp.lmapDomain k k f (Finsupp.single h a))
      simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_mul] }

/-- The actual group-ring map preserves the literal augmentation. -/
theorem originalRegularGroupChange_augmentation (x : Rep.leftRegular k G) :
    (originalAugmentation k H).hom ((originalRegularGroupChange (k := k) f).hom x) =
      (originalAugmentation k G).hom x := by
  rw [originalAugmentation_apply, originalAugmentation_apply]
  change Finsupp.linearCombination k (fun _ : H => (1 : k))
    (Finsupp.mapDomain f x) = _
  rw [Finsupp.linearCombination_mapDomain]
  rfl

/-- The literal group-ring map restricts to the actual augmentation ideals. -/
def originalAugmentationGroupChange :
    originalAugmentationIdeal k G ⟶ Rep.res f (originalAugmentationIdeal k H) :=
  Rep.ofHom {
    toLinearMap := ((originalRegularGroupChange (k := k) f).hom.toLinearMap.comp
      (LinearMap.ker (originalAugmentation k G).hom.toLinearMap).subtype).codRestrict _
        (fun x => (originalRegularGroupChange_augmentation f x.val).trans x.property)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact Rep.hom_comm_apply (originalRegularGroupChange (k := k) f) g x.val }

/-- The literal group-ring and augmentation maps form the actual
group-change diagram of augmentation sequences. -/
def originalAugmentationGroupChangeSequenceMap :
    originalAugmentationShortComplex k G ⟶
      (originalAugmentationShortComplex k H).map (Rep.resFunctor f) where
  τ₁ := originalAugmentationGroupChange f
  τ₂ := originalRegularGroupChange f
  τ₃ := 𝟙 (Rep.trivial k G k)
  comm₁₂ := rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    exact originalRegularGroupChange_augmentation f

end
end Dubon2026
