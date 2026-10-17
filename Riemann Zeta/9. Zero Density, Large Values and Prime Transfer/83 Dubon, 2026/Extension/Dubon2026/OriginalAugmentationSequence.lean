import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The literal augmentation sequence

The fundamental-class extension on the DUB-17 finite class/Ext route has
this augmentation ideal as its quotient. The regular representation,
augmentation and kernel are actual objects. This supplies the coefficient
sequence needed to derive the splitting coefficient's subgroup H1/H2
vanishing, rather than taking those vanishing statements as inputs.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (k G : Type) [CommRing k] [Group G]

/-- The usual augmentation of the actual group ring. -/
abbrev originalAugmentation : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.leftRegularHom (Rep.trivial k G k) 1

/-- The augmentation ideal, with the inherited group action. -/
abbrev originalAugmentationIdeal : Rep k G :=
  Rep.of (Representation.subrepresentation (Rep.leftRegular k G).ρ
    (LinearMap.ker (originalAugmentation k G).hom.toLinearMap) fun g x hx => by
      change (originalAugmentation k G).hom x = 0 at hx
      change (originalAugmentation k G).hom ((Rep.leftRegular k G).ρ g x) = 0
      rw [Rep.hom_comm_apply, hx, map_zero])

/-- The original augmentation ideal's literal inclusion. -/
def originalAugmentationInclusion : originalAugmentationIdeal k G ⟶ Rep.leftRegular k G :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

/-- The original augmentation coefficient complex. -/
def originalAugmentationShortComplex : ShortComplex (Rep k G) where
  X₁ := originalAugmentationIdeal k G
  X₂ := Rep.leftRegular k G
  X₃ := Rep.trivial k G k
  f := originalAugmentationInclusion k G
  g := originalAugmentation k G
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.property))

/-- Augmentation sums the actual coefficients. -/
theorem originalAugmentation_apply (f : G →₀ k) :
    (originalAugmentation k G).hom f = Finsupp.linearCombination k (fun _ : G => (1 : k)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single g r =>
    rw [Rep.leftRegularHom_hom_single, Finsupp.linearCombination_single]
    rfl

/-- Membership in the literal augmentation ideal is the zero-sum condition. -/
theorem originalAugmentationIdeal_mem (f : G →₀ k) :
    f ∈ LinearMap.ker (originalAugmentation k G).hom.toLinearMap ↔
      Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 := by
  rw [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply,
    originalAugmentation_apply]

/-- The actual augmentation sequence is short exact. -/
theorem originalAugmentationShortComplex_shortExact :
    (originalAugmentationShortComplex k G).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun x y h => Subtype.ext h)
    epi_g := (Rep.epi_iff_surjective _).mpr ?_ }
  · apply ((originalAugmentationShortComplex k G).exact_map_iff_of_faithful
      (forget₂ (Rep k G) (ModuleCat k))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact Submodule.range_subtype _
  · intro z
    change k at z
    refine ⟨Finsupp.single 1 z, ?_⟩
    change (originalAugmentation k G).hom (Finsupp.single 1 z) = z
    rw [originalAugmentation_apply, Finsupp.linearCombination_single]
    change z * (1 : k) = z
    exact mul_one z

/-- Translation on the ideal is literal translation on the group-ring support. -/
theorem originalAugmentationIdeal_action (g : G) (x : originalAugmentationIdeal k G) :
    ((originalAugmentationIdeal k G).ρ g x : G →₀ k) =
      Finsupp.lmapDomain k k (g * ·) (x : G →₀ k) := rfl

end
end Dubon2026
