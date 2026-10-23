import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! Exact field degree of a reduced polynomial quotient.
The native rational-function degree theorem applies once the actual kernel
denominator is monic and coprime to the numerator. This is used for the odd
cyclic quotient on the DUB-17/18 field-embedding dependency chain. -/

open Polynomial
open scoped IntermediateField

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] {p q : F[X]}

/-- A coprime polynomial quotient with monic denominator is already normalized. -/
theorem ratFunc_num_denom_of_coprime_monic (hc : IsCoprime p q) (hq : q.Monic) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).num = p ∧
      (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).denom = q := by
  classical
  have hg : gcd p q = 1 := by
    rw [← NormalizedGCDMonoid.normalize_gcd, normalize_eq_one]
    exact (gcd_isUnit_iff p q).mpr hc
  rw [RatFunc.num_div, RatFunc.denom_div _ hq.ne_zero, hg]
  simp [hq.leadingCoeff]

/-- The polynomial quotient defines a field extension of degree its larger numerator degree. -/
theorem finrank_ratFunc_div_of_coprime_monic (hc : IsCoprime p q) (hq : q.Monic)
    (hdeg : q.natDegree ≤ p.natDegree) :
    Module.finrank F⟮algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q⟯
      (RatFunc F) = p.natDegree := by
  obtain ⟨hn, hd⟩ := ratFunc_num_denom_of_coprime_monic hc hq
  rw [RatFunc.finrank_eq_max_natDegree, hn, hd, max_eq_left hdeg]

end Dubon2026.SourceEllipticFunctionField
