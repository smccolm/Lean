import Dubon2026.OriginalQuotientSubgroupPreimage

/-! # Literal invariant coefficients over a quotient subgroup

The two-degree vanishing criterion transfers restrictions of quotient
invariants to the actual preimage subgroup. Both coefficient maps below
retain the original elements and actions. The pinned first isomorphism
theorem identifies the acting groups; no invariant-comparison premise is
left for the later subgroup induction in DUB-17's class/Ext route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
  (S : Subgroup G) [S.Normal] (T : Subgroup (G ⧸ S))

/-- An element is invariant under the original normal subgroup exactly when it is invariant under that subgroup inside the literal preimage. -/
theorem originalQuotientSubgroup_invariants_iff (x : A) :
    x ∈ Representation.invariants (A.ρ.comp S.subtype) ↔
      x ∈ Representation.invariants ((Rep.res (T.comap (QuotientGroup.mk' S)).subtype A).ρ.comp
        (S.subgroupOf (T.comap (QuotientGroup.mk' S))).subtype) := by
  constructor
  · intro h g
    exact h ⟨g.val.val, g.property⟩
  · intro h g
    exact h ⟨⟨g.val, originalQuotientSubgroup_le_preimage S T g.property⟩, g.property⟩

/-- The original quotient-subgroup invariant coefficients map identically to the invariants of the literal preimage. -/
def originalQuotientSubgroupInvariantHom :
    Rep.res (originalQuotientSubgroupPreimageEquiv S T).toMonoidHom
      (Rep.res T.subtype (A.quotientToInvariants S)) ⟶
    (Rep.res (T.comap (QuotientGroup.mk' S)).subtype A).quotientToInvariants
      (S.subgroupOf (T.comap (QuotientGroup.mk' S))) :=
  Rep.ofHom ⟨{
    toFun := fun x => ⟨x.val, (originalQuotientSubgroup_invariants_iff A S T x.val).mp x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }, by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g => rfl⟩

/-- The actual invariant coefficient comparison is an isomorphism. -/
theorem originalQuotientSubgroupInvariantHom_isIso :
    IsIso (originalQuotientSubgroupInvariantHom A S T) := by
  haveI : Mono (originalQuotientSubgroupInvariantHom A S T) :=
    (Rep.mono_iff_injective _).mpr (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : (Rep.res (T.comap (QuotientGroup.mk' S)).subtype A).quotientToInvariants
        (S.subgroupOf (T.comap (QuotientGroup.mk' S))) => z.val) h)
  haveI : Epi (originalQuotientSubgroupInvariantHom A S T) :=
    (Rep.epi_iff_surjective _).mpr (fun x =>
      ⟨⟨x.val, (originalQuotientSubgroup_invariants_iff A S T x.val).mpr x.property⟩, rfl⟩)
  exact isIso_of_mono_of_epi _

end
end Dubon2026
