import Mathlib.GroupTheory.Coset.Basic

/-! # Literal subgroup coordinates of the original group -/

namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] (S : Subgroup G)

/-- Choose a representative of the actual left coset of the original element. -/
def subgroupCosetRepresentative (g : G) : G := (QuotientGroup.mk g : G ⧸ S).out

/-- The actual remaining subgroup element after removing that representative. -/
def subgroupCosetRemainder (g : G) : S :=
  ⟨(subgroupCosetRepresentative S g)⁻¹ * g,
    QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' _))⟩

/-- The original element is exactly its chosen coset representative times
its actual subgroup remainder. -/
theorem subgroupCosetRepresentative_mul_remainder (g : G) :
    subgroupCosetRepresentative S g * (subgroupCosetRemainder S g : G) = g := by
  exact mul_inv_cancel_left _ _

/-- Right multiplication by an original subgroup element preserves the
actual left coset and hence its same chosen representative. -/
theorem subgroupCosetRepresentative_mul (g : G) (h : S) :
    subgroupCosetRepresentative S (g * h) = subgroupCosetRepresentative S g := by
  unfold subgroupCosetRepresentative
  rw [QuotientGroup.mk_mul_of_mem g h.property]

/-- The actual subgroup remainder is equivariant for right multiplication
by the original subgroup. -/
theorem subgroupCosetRemainder_mul (g : G) (h : S) :
    subgroupCosetRemainder S (g * h) = subgroupCosetRemainder S g * h := by
  apply Subtype.ext
  change (subgroupCosetRepresentative S (g * h))⁻¹ * (g * h) =
    ((subgroupCosetRepresentative S g)⁻¹ * g) * h
  rw [subgroupCosetRepresentative_mul, mul_assoc]

end
end Dubon2026
