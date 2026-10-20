import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Quotients of the actual auxiliary level subgroups

The BLGG finite auxiliary set uses the original ambient local matrix
groups. This identifies the quotient of their product subgroups with
the product of the original local quotients, retaining both levels.
-/

namespace Dubon2026

noncomputable section

variable {S : Type*} {G : S → Type*} [∀ s, Group (G s)]
variable (U V : ∀ s, Subgroup (G s))
variable [∀ s, ((V s).subgroupOf (U s)).Normal]

/-- Coordinate reduction on the actual product level. -/
def auxiliarySubgroupFamilyReduction :
    Subgroup.pi Set.univ U →* (∀ s, U s ⧸ (V s).subgroupOf (U s)) where
  toFun x s := QuotientGroup.mk' ((V s).subgroupOf (U s)) ⟨x.val s, x.property s (Set.mem_univ s)⟩
  map_one' := funext fun _ => rfl
  map_mul' x y := funext fun s =>
    (QuotientGroup.mk' ((V s).subgroupOf (U s))).map_mul
      ⟨x.val s, x.property s (Set.mem_univ s)⟩ ⟨y.val s, y.property s (Set.mem_univ s)⟩

/-- Every tuple of original local quotient classes lifts to the actual product level. -/
theorem auxiliarySubgroupFamilyReduction_surjective :
    Function.Surjective (auxiliarySubgroupFamilyReduction U V) := by
  intro y
  choose x hx using fun s => QuotientGroup.mk'_surjective ((V s).subgroupOf (U s)) (y s)
  refine ⟨⟨fun s => (x s).val, fun s _ => (x s).property⟩, ?_⟩
  exact funext hx

/-- The actual lower product level is exactly the coordinate reduction kernel. -/
theorem auxiliarySubgroupFamilyReduction_ker :
    (auxiliarySubgroupFamilyReduction U V).ker =
      (Subgroup.pi Set.univ V).subgroupOf (Subgroup.pi Set.univ U) := by
  ext x
  change (auxiliarySubgroupFamilyReduction U V x = 1) ↔
    ∀ s ∈ Set.univ, x.val s ∈ V s
  rw [funext_iff]
  simp only [Set.mem_univ, forall_const]
  exact forall_congr' fun s => QuotientGroup.eq_one_iff (N := (V s).subgroupOf (U s))
    (⟨x.val s, x.property s (Set.mem_univ s)⟩ : U s)

/-- Normality of the actual lower product level follows from the kernel computation. -/
instance auxiliarySubgroupFamily_normal :
    ((Subgroup.pi Set.univ V).subgroupOf (Subgroup.pi Set.univ U)).Normal := by
  rw [← auxiliarySubgroupFamilyReduction_ker U V]
  infer_instance

/-- The literal product-level quotient is the product of the original local quotients. -/
def auxiliarySubgroupFamilyQuotientEquiv :
    Subgroup.pi Set.univ U ⧸
      (Subgroup.pi Set.univ V).subgroupOf (Subgroup.pi Set.univ U) ≃*
        (∀ s, U s ⧸ (V s).subgroupOf (U s)) :=
  (QuotientGroup.quotientMulEquivOfEq (auxiliarySubgroupFamilyReduction_ker U V).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (auxiliarySubgroupFamilyReduction U V)
      (auxiliarySubgroupFamilyReduction_surjective U V))

end
end Dubon2026
