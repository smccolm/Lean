import Dubon2026.OriginalAugmentationInvariantImage
import Dubon2026.OriginalInvariantConnectingKernel

/-! # The original augmentation connecting map and its exact kernel

The genuine H0-to-H1 connecting map is expressed on the actual integers.
Its kernel is calculated using exactness and the proved augmentation
image on subgroup invariants. This identifies the H1 group needed for
the fundamental-class splitting coefficient on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (S : Subgroup G)

/-- The genuine augmentation connecting map, using the canonical H0 identification for trivial integers. -/
def originalAugmentationConnecting :
    ℤ →ₗ[ℤ] groupCohomology (Rep.res S.subtype (originalAugmentationIdeal ℤ G)) 1 :=
  (groupCohomology.δ (originalAugmentationSubgroup_shortExact (k := ℤ) S) 0 1 rfl).hom.comp
    (groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℤ S ℤ)).inv.hom

/-- Every original augmentation-ideal H1 class comes from the genuine integer connecting map. -/
theorem originalAugmentationConnecting_surjective [Finite G] :
    Function.Surjective (originalAugmentationConnecting S) := by
  have hd := groupCohomology.epi_δ_of_isZero
    (originalAugmentationSubgroup_shortExact (k := ℤ) S) 0
    (originalRegularSubgroup_positive_zero (k := ℤ) S 0)
  have hs := (ModuleCat.epi_iff_surjective _).mp hd
  exact hs.comp
    (groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℤ S ℤ)).toLinearEquiv.symm.surjective

/-- The genuine connecting map kills exactly the augmentation images of actual subgroup invariants. -/
theorem originalAugmentationConnecting_eq_zero_iff_invariant (z : ℤ) :
    originalAugmentationConnecting S z = 0 ↔
      ∃ x : Rep.leftRegular ℤ G,
        x ∈ (Rep.res S.subtype (Rep.leftRegular ℤ G)).ρ.invariants ∧
          (originalAugmentation ℤ G).hom x = z := by
  exact originalInvariantConnecting_zero_iff
    (originalAugmentationSubgroup_shortExact (k := ℤ) S) ⟨z, fun _ => rfl⟩

/-- The exact kernel of the original connecting map consists of the subgroup-order multiples. -/
theorem originalAugmentationConnecting_eq_zero_iff [Finite G] [Fintype S] (z : ℤ) :
    originalAugmentationConnecting S z = 0 ↔ ∃ w : ℤ, (Fintype.card S : ℤ) * w = z :=
  (originalAugmentationConnecting_eq_zero_iff_invariant S z).trans
    (originalAugmentationInvariant_image_iff S z)

end
end Dubon2026
