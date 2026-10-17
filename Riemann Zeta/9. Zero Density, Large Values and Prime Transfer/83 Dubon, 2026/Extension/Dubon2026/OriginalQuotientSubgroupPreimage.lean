import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual preimages of subgroups in the normal quotient

The finite class/Ext two-degree criterion needs subgroup vanishing to
descend to quotient-group invariants. Retain the literal preimage subgroup
and its quotient, using the pinned first isomorphism theorem. This is the
group comparison needed before transporting its invariant coefficients.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {G : Type} [Group G] (S : Subgroup G) [S.Normal] (T : Subgroup (G ⧸ S))

/-- The original quotient homomorphism restricted to the literal preimage of the chosen subgroup. -/
def originalQuotientSubgroupPreimageHom :
    T.comap (QuotientGroup.mk' S) →* T := (QuotientGroup.mk' S).subgroupComap T

/-- Every original normal-subgroup element belongs to that literal preimage. -/
theorem originalQuotientSubgroup_le_preimage : S ≤ T.comap (QuotientGroup.mk' S) := by
  intro g hg
  change QuotientGroup.mk g ∈ T
  rw [(QuotientGroup.eq_one_iff g).mpr hg]
  exact T.one_mem

/-- The restricted quotient map is surjective by the pinned subgroup-comap theorem. -/
theorem originalQuotientSubgroupPreimageHom_surjective :
    Function.Surjective (originalQuotientSubgroupPreimageHom S T) :=
  MonoidHom.subgroupComap_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective S)

/-- Its kernel is precisely the original normal subgroup viewed inside the literal preimage. -/
theorem originalQuotientSubgroupPreimageHom_ker :
    (originalQuotientSubgroupPreimageHom S T).ker = S.subgroupOf (T.comap (QuotientGroup.mk' S)) := by
  ext g
  change (⟨QuotientGroup.mk g.val, g.property⟩ : T) = 1 ↔ g.val ∈ S
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff g.val

/-- The actual preimage quotient is the original subgroup in the quotient group. -/
def originalQuotientSubgroupPreimageEquiv :
    (T.comap (QuotientGroup.mk' S) ⧸ S.subgroupOf (T.comap (QuotientGroup.mk' S))) ≃* T :=
  (QuotientGroup.quotientMulEquivOfEq (originalQuotientSubgroupPreimageHom_ker S T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (originalQuotientSubgroupPreimageHom S T)
      (originalQuotientSubgroupPreimageHom_surjective S T))

/-- The preimage quotient equivalence preserves the literal original quotient coordinate. -/
theorem originalQuotientSubgroupPreimageEquiv_mk (g : T.comap (QuotientGroup.mk' S)) :
    originalQuotientSubgroupPreimageEquiv S T (QuotientGroup.mk g) =
      originalQuotientSubgroupPreimageHom S T g := rfl

end
end Dubon2026
