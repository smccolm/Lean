import Dubon2026.SourceCurvePlaceRestriction
import Dubon2026.SourceLaurentReindex
import Mathlib.RingTheory.LaurentSeries

/-! DUB-17/18 -> numerical modular genus -> cusp classification -> places
from the actual Laurent embeddings. Pinned Laurent valuation and Hahn
order formulas give the precise valuation-ring membership criterion.
This supplies a direct integer-valued route to the restricted place,
without introducing rational-exponent series or a Puiseux field.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open WithZero
variable {K : Type*} [Field K]

theorem laurent_order_inv (f : LaurentSeries K) : f⁻¹.order = -f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [inv_zero, HahnSeries.order_zero, neg_zero]
  have h := HahnSeries.order_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, HahnSeries.order_one] at h
  omega

theorem laurent_order_zpow (f : LaurentSeries K) (n : ℤ) :
    (f ^ n).order = n * f.order := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, HahnSeries.order_pow, nsmul_eq_mul]
  | negSucc n =>
    rw [zpow_negSucc, laurent_order_inv, HahnSeries.order_pow]
    simp only [nsmul_eq_mul, Int.negSucc_eq, Nat.cast_add, Nat.cast_one, neg_mul]

theorem laurent_valuation_mem_iff (f : LaurentSeries K) :
    f ∈ (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).valuationSubring ↔ 0 ≤ f.order := by
  change Valued.v f ≤ 1 ↔ _
  rw [← WithZero.exp_zero, ← neg_zero, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  constructor
  · intro h
    rcases eq_or_ne f 0 with rfl | hf
    · rw [HahnSeries.order_zero]; omega
    · by_contra hn
      exact hf (HahnSeries.coeff_order_eq_zero.mp (h f.order (lt_of_not_ge hn)))
  · intro h n hn
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn h)

end
end Dubon2026.SourceFunctionField
