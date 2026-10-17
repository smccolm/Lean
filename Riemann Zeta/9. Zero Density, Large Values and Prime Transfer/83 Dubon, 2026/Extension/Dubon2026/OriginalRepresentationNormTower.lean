import Dubon2026.OriginalCoinducedGlobalDimensionShift
import Mathlib.GroupTheory.Coset.Basic

/-! # The literal subgroup and quotient representation norms

The finite class/Ext two-degree criterion also needs norm preimages in
degree zero. This is its normal-subgroup step: the actual group norm is
the quotient norm of the actual subgroup norm. The existing original
coset coordinates and invariant action retain the required normalization.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (A : Rep.{0} k G) (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- The proved original coset coordinates give a bijection retaining the literal representative product. -/
def originalNormCosetEquiv : G ≃ (G ⧸ S) × S where
  toFun g := (QuotientGroup.mk g, subgroupCosetRemainder S g)
  invFun z := z.1.out * z.2
  left_inv g := subgroupCosetRepresentative_mul_remainder S g
  right_inv z := by
    rcases z with ⟨q, s⟩
    apply Prod.ext
    · change (QuotientGroup.mk (q.out * s) : G ⧸ S) = q
      rw [QuotientGroup.mk_mul_of_mem _ s.property, QuotientGroup.out_eq']
    · apply Subtype.ext
      change (subgroupCosetRepresentative S (q.out * s))⁻¹ * (q.out * s) = s
      rw [subgroupCosetRepresentative_mul]
      simp [subgroupCosetRepresentative]

/-- The actual subgroup norm has values in the original normal-invariant coefficient. -/
def originalSubgroupNormToInvariants : A →ₗ[k] A.quotientToInvariants S :=
  (Rep.res S.subtype A).ρ.norm.codRestrict _ (fun x s =>
    Representation.self_norm_apply (Rep.res S.subtype A).ρ s x)

omit [Fintype G] [Fintype S] [Fintype (G ⧸ S)] in
/-- The original quotient action agrees with the actual action of any chosen coset representative. -/
theorem originalQuotientInvariant_action_out (q : G ⧸ S) (x : A.quotientToInvariants S) :
    ((A.quotientToInvariants S).ρ q x).val = A.ρ q.out x.val := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

/-- The actual full-group norm is the actual quotient norm of the actual subgroup norm. -/
theorem originalRepresentation_norm_tower (x : A) :
    ((A.quotientToInvariants S).ρ.norm (originalSubgroupNormToInvariants A S x)).val = A.ρ.norm x := by
  have ht : ((A.quotientToInvariants S).ρ.norm (originalSubgroupNormToInvariants A S x)).val =
      ∑ q : G ⧸ S, A.ρ q.out ((Rep.res S.subtype A).ρ.norm x) := by
    simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro q _
    simpa only [originalSubgroupNormToInvariants, LinearMap.codRestrict_apply,
      Representation.norm, LinearMap.sum_apply] using
      originalQuotientInvariant_action_out A S q (originalSubgroupNormToInvariants A S x)
  rw [ht]
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  calc
    (∑ q : G ⧸ S, ∑ s : S, A.ρ q.out ((Rep.res S.subtype A).ρ s x)) =
        ∑ z : (G ⧸ S) × S, A.ρ (z.1.out * z.2) x := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      exact (LinearMap.congr_fun (A.ρ.map_mul q.out s.val) x).symm
    _ = ∑ g : G, A.ρ g x := by
      change (∑ z : (G ⧸ S) × S, A.ρ ((originalNormCosetEquiv S).symm z) x) = _
      exact Equiv.sum_comp (originalNormCosetEquiv S).symm (fun g => A.ρ g x)

/-- Genuine subgroup and quotient invariant-norm preimages construct a full-group invariant-norm preimage. -/
theorem originalNorm_preimages_of_subgroup_quotient
    (hS : ∀ x : A, x ∈ (Rep.res S.subtype A).ρ.invariants →
      ∃ y : A, (Rep.res S.subtype A).ρ.norm y = x)
    (hQ : ∀ x : A.quotientToInvariants S, x ∈ (A.quotientToInvariants S).ρ.invariants →
      ∃ y : A.quotientToInvariants S, (A.quotientToInvariants S).ρ.norm y = x)
    (x : A) (hx : x ∈ A.ρ.invariants) : ∃ y : A, A.ρ.norm y = x := by
  let xS : A.quotientToInvariants S := ⟨x, fun s => hx s.val⟩
  have hxS : xS ∈ (A.quotientToInvariants S).ρ.invariants := by
    intro q
    apply Subtype.ext
    rw [originalQuotientInvariant_action_out]
    exact hx q.out
  obtain ⟨y, hy⟩ := hQ xS hxS
  obtain ⟨z, hz⟩ := hS y.val y.property
  have hzy : originalSubgroupNormToInvariants A S z = y := Subtype.ext hz
  refine ⟨z, ?_⟩
  rw [← originalRepresentation_norm_tower A S z, hzy, hy]

end
end Dubon2026
