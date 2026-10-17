import Dubon2026.OriginalRegularSubgroupAcyclicity
import Dubon2026.OriginalTrivialIntegerFirstVanishing

/-! # The actual augmentation sequence on every original subgroup

The same augmentation maps stay exact on restriction. Existing regular
coefficient acyclicity and trivial-integer H1 vanishing compute the ideal's
H2 without a separate dimension-shift object. Its H1 cardinality is the
remaining input to the fundamental splitting argument for DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]

/-- The literal augmentation sequence remains short exact on every actual subgroup. -/
theorem originalAugmentationSubgroup_shortExact (S : Subgroup G) :
    ((originalAugmentationShortComplex k G).map (Rep.resFunctor S.subtype)).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr ?_ }
  · apply (((originalAugmentationShortComplex k G).map (Rep.resFunctor S.subtype)).exact_map_iff_of_faithful
      (forget₂ (Rep k S) (ModuleCat k))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact Submodule.range_subtype _
  · intro z
    change k at z
    refine ⟨Finsupp.single 1 z, ?_⟩
    change (originalAugmentation k G).hom (Finsupp.single 1 z) = z
    rw [originalAugmentation_apply, Finsupp.linearCombination_single]
    change z * (1 : k) = z
    exact mul_one z

/-- The original integral augmentation ideal has vanishing second cohomology on every subgroup of a finite group. -/
theorem originalAugmentationSubgroup_second_zero [Finite G] (S : Subgroup G) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalAugmentationIdeal ℤ G)) 2) := by
  have hi := groupCohomology.isIso_δ_of_isZero
    (originalAugmentationSubgroup_shortExact (k := ℤ) S) 1
    (originalRegularSubgroup_positive_zero (k := ℤ) S 0)
    (originalRegularSubgroup_positive_zero (k := ℤ) S 1)
  have hz : Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
    originalTrivialInteger_first_zero S
  exact hz.of_iso (@asIso _ _ _ _
    (groupCohomology.δ (originalAugmentationSubgroup_shortExact (k := ℤ) S) 1 2 rfl) hi).symm

end
end Dubon2026
