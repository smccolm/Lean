import Dubon2026.SourceCurveAdeleLocalQuotient
import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> full original Picard-period Hecke comparison -> moving
divisors away from cusps -> finite prescribed orders. These elementary
valuation identities support the finite-place separating functions and
indicators; no approximation theorem is assumed.
Adapted from S_AlgebraicCurve_Place_exists_forall_ord_eq,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. The existing local
order/valuation equality and unequal-order addition theorem are reused.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_lt_one_iff_ord_pos {x : F} (hx : x ≠ 0) :
    v.adicValuation x < 1 ↔ 0 < v.ord x := by
  rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_lt_exp, neg_lt_zero]

theorem one_lt_adicValuation_iff_ord_neg {x : F} (hx : x ≠ 0) :
    1 < v.adicValuation x ↔ v.ord x < 0 := by
  rw [v.adicValuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_lt_exp, neg_pos]

theorem one_add_ne_zero_and_ord_eq_of_ord_neg {t : F} (ht : v.ord t < 0) :
    1 + t ≠ 0 ∧ v.ord (1 + t) = v.ord t := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hval : v.adicValuation 1 < v.adicValuation t := by
    rw [map_one]
    exact (v.one_lt_adicValuation_iff_ord_neg ht0).mpr ht
  have hsum := v.adicValuation.map_add_eq_of_lt_right hval
  have hne : (1 : F) + t ≠ 0 := by
    intro h
    rw [h, map_zero] at hsum
    exact v.adicValuation_ne_zero ht0 hsum.symm
  refine ⟨hne, ?_⟩
  simp only [Place.ord, hsum]

theorem ord_one_add_of_ord_pos {t : F} (ht : 0 < v.ord t) :
    v.ord (1 + t) = 0 := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  simpa only [ord_one] using v.ord_add_eq_of_lt one_ne_zero ht0 (by simpa only [ord_one])

end
end Dubon2026.SourceCurve.Place
