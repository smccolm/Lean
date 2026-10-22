import Dubon2026.SourceCurveLocalDifferentials
import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> arithmetic Picard injectivity -> principal-divisor descent
-> trace regularity at a new constant-field value. A nonzero constant plus
a positive-order function has order zero, by the existing strict order law.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

theorem ord_algebraMap_add_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {a : K} (ha : a ≠ 0) {f : F} (hf : 0 < v.ord f) :
    v.ord (algebraMap K F a + f) = 0 := by
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hf
    exact (lt_irrefl 0) hf
  rw [v.ord_add_eq_of_lt ((map_ne_zero _).mpr ha) hf0 (by
    rw [v.ord_algebraMap]
    exact hf), v.ord_algebraMap]

end
end Dubon2026.SourceCurve.ConstantField
