import Dubon2026.SourceIntegralHeckeConjugation

/-! Composition of the actual diagonal conjugations through the product subgroup.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> original integral H1 Hecke commutativity -> composition of distinct-prime
correspondences through the original upper subgroup at their product.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Membership in the actual upper Hecke subgroup is its literal integral divisibility condition. -/
theorem sourceHeckeUpper_mem_iff (Q n : ℕ) (g : Gamma0 Q) :
    g ∈ heckeUpperSubgroup Q n ↔ (n : ℤ) ∣ g.val 0 1 :=
  ZMod.intCast_zmod_eq_zero_iff_dvd _ n

/-- The actual upper subgroup at a product is contained in the subgroup at its first factor. -/
theorem sourceHeckeUpper_product_le (Q a b : ℕ) :
    heckeUpperSubgroup Q (a * b) ≤ heckeUpperSubgroup Q a := by
  intro g hg
  rw [sourceHeckeUpper_mem_iff] at hg ⊢
  exact (show (a : ℤ) ∣ (a * b : ℕ) by
    rw [Nat.cast_mul]; exact dvd_mul_right _ _).trans hg

/-- The actual product-subgroup inclusion into the first factor subgroup. -/
def sourceHeckeProductToLeft (Q a b : ℕ) :
    heckeUpperSubgroup Q (a * b) →* heckeUpperSubgroup Q a :=
  Subgroup.inclusion (sourceHeckeUpper_product_le Q a b)

/-- The literal first-factor conjugation lands in the second upper subgroup exactly
when the original matrix lies in the product subgroup. -/
theorem sourceHeckeUpper_product_mem_iff (Q a b : ℕ) [NeZero a]
    (g : heckeUpperSubgroup Q a) :
    g.val ∈ heckeUpperSubgroup Q (a * b) ↔
      sourceIntegralHeckeConjugate g ∈ heckeUpperSubgroup Q b := by
  rw [sourceHeckeUpper_mem_iff, sourceHeckeUpper_mem_iff]
  change ((a * b : ℕ) : ℤ) ∣ g.val.val 0 1 ↔
    (b : ℤ) ∣ g.val.val 0 1 / (a : ℤ)
  obtain ⟨d, hd⟩ := (sourceHeckeUpper_mem_iff Q a g.val).mp g.property
  rw [hd, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne a)),
    Nat.cast_mul]
  exact mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr (NeZero.ne a))

/-- The first conjugate of an actual product-subgroup element is an actual second-factor element. -/
def sourceHeckeProductToRight (Q a b : ℕ) [NeZero a]
    (g : heckeUpperSubgroup Q (a * b)) : heckeUpperSubgroup Q b :=
  ⟨sourceIntegralHeckeConjugate (sourceHeckeProductToLeft Q a b g),
    (sourceHeckeUpper_product_mem_iff Q a b _).mp g.property⟩

/-- Integral conjugation at the product is exactly the successive original diagonal conjugations. -/
theorem sourceHeckeConjugate_product (Q a b : ℕ) [NeZero a]
    (g : heckeUpperSubgroup Q (a * b)) :
    sourceIntegralHeckeConjugate g =
      sourceIntegralHeckeConjugate (sourceHeckeProductToRight Q a b g) := by
  apply Subtype.ext
  apply Subtype.ext
  change !![g.val.val 0 0, g.val.val 0 1 / ((a * b : ℕ) : ℤ);
      g.val.val 1 0 * ((a * b : ℕ) : ℤ), g.val.val 1 1] =
    !![g.val.val 0 0, (g.val.val 0 1 / (a : ℤ)) / (b : ℤ);
      (g.val.val 1 0 * (a : ℤ)) * (b : ℤ), g.val.val 1 1]
  rw [Int.ediv_ediv_of_nonneg (by positivity), Nat.cast_mul, mul_assoc]

end
end Dubon2026
