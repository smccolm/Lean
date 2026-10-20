import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The source level quotient under original surjective evaluation

Original local evaluation pulls the two source levels back into the
principal unitary level. Surjectivity and the exact kernel compute the
quotient, retaining both subgroups. This is the remaining group bridge
for DUB-17's actual small auxiliary unitary family.
-/

namespace Dubon2026
noncomputable section

variable {G A : Type*} [Group G] [Group A]
variable (U V : Subgroup A) (f : G →* A)

/-- Original evaluation restricted to the inverse image of the source upper level. -/
def subgroupPairPreimageMap : U.comap f →* U :=
  (f.comp (U.comap f).subtype).codRestrict U (fun x => x.property)

/-- Surjective original evaluation lifts every element of the original upper level. -/
theorem subgroupPairPreimageMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (subgroupPairPreimageMap U f) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  have hm : x ∈ U.comap f := by
    change f x ∈ U
    rw [hx]
    exact y.property
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

/-- The original lower preimage level is normal inside the upper preimage level. -/
theorem subgroupPairPreimage_normal [(V.subgroupOf U).Normal] :
    ((V.comap f).subgroupOf (U.comap f)).Normal :=
  Subgroup.Normal.comap (inferInstance : (V.subgroupOf U).Normal) (subgroupPairPreimageMap U f)

/-- The original lower preimage level is exactly the original quotient reduction kernel. -/
theorem subgroupPairPreimage_kernel [(V.subgroupOf U).Normal] :
    (V.comap f).subgroupOf (U.comap f) =
      ((QuotientGroup.mk' (V.subgroupOf U)).comp (subgroupPairPreimageMap U f)).ker := by
  ext x
  exact (QuotientGroup.eq_one_iff (N := V.subgroupOf U) (subgroupPairPreimageMap U f x)).symm

/-- The actual quotient of the two inverse image levels is the original source quotient under surjective evaluation. -/
def subgroupPairPreimageQuotientEquiv [(V.subgroupOf U).Normal]
    [((V.comap f).subgroupOf (U.comap f)).Normal] (hf : Function.Surjective f) :
    U.comap f ⧸ (V.comap f).subgroupOf (U.comap f) ≃* U ⧸ V.subgroupOf U :=
  (QuotientGroup.quotientMulEquivOfEq (subgroupPairPreimage_kernel U V f)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (subgroupPairPreimageMap_surjective U f hf)))

end
end Dubon2026
