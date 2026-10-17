import Dubon2026.OriginalQuotientSubgroupInvariants
import Dubon2026.OriginalPositiveInflationComparison

/-! # Transfer actual subgroup vanishing to quotient invariants

This discharges the subgroup-comparison input in the finite class/Ext
two-degree criterion. All coefficients are original restrictions and
normal invariants; the group and coefficient isomorphisms are constructed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/-- Restricting the same original subgroup through a larger subgroup preserves positive vanishing. -/
theorem originalSubgroupOf_positive_zero (S E : Subgroup G) (hSE : S ≤ E)
    (h : ∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (n + 1)))
    (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res (S.subgroupOf E).subtype (Rep.res E.subtype A)) (n + 1)) := by
  let e := Subgroup.subgroupOfEquivOfLe hSE
  let B := Rep.res (S.subgroupOf E).subtype (Rep.res E.subtype A)
  let φ : Rep.res e.toMonoidHom (Rep.res S.subtype A) ⟶ B := 𝟙 B
  haveI : IsIso φ := by change IsIso (𝟙 B); infer_instance
  have hi : IsIso (groupCohomology.map e.toMonoidHom φ (n + 1)) :=
    originalGroupChangeCohomology_isIso (Rep.res S.subtype A) B e φ (n + 1)
  exact (h n).of_iso (@asIso _ _ _ _ _ hi).symm

/-- Positive vanishing on the actual preimage descends to the quotient subgroup when the original normal subgroup is positively acyclic. -/
theorem originalQuotientSubgroup_zero_of_preimage (S : Subgroup G) [S.Normal]
    (T : Subgroup (G ⧸ S))
    (hS : ∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (n + 1)))
    (n : ℕ)
    (hE : Limits.IsZero (groupCohomology (Rep.res (T.comap (QuotientGroup.mk' S)).subtype A) (n + 1))) :
    Limits.IsZero (groupCohomology (Rep.res T.subtype (A.quotientToInvariants S)) (n + 1)) := by
  let E := T.comap (QuotientGroup.mk' S)
  let N := S.subgroupOf E
  let B := Rep.res E.subtype A
  have hN : ∀ m : ℕ, Limits.IsZero (groupCohomology (Rep.res N.subtype B) (m + 1)) :=
    originalSubgroupOf_positive_zero A S E (originalQuotientSubgroup_le_preimage S T) hS
  have hi := originalPositiveInflation_isIso_of_subgroup_zero B N hN n
  have hQ : Limits.IsZero (groupCohomology (B.quotientToInvariants N) (n + 1)) :=
    hE.of_iso (@asIso _ _ _ _ _ hi)
  haveI : IsIso (originalQuotientSubgroupInvariantHom A S T) :=
    originalQuotientSubgroupInvariantHom_isIso A S T
  have he := originalGroupChangeCohomology_isIso (Rep.res T.subtype (A.quotientToInvariants S))
    (B.quotientToInvariants N) (originalQuotientSubgroupPreimageEquiv S T)
    (originalQuotientSubgroupInvariantHom A S T) (n + 1)
  exact hQ.of_iso (@asIso _ _ _ _ _ he)

end
end Dubon2026
