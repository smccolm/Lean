import Mathlib.NumberTheory.LocalField.Basic

/-! # The original local-field valuation with its normalized integer unit order -/

namespace Dubon2026
noncomputable section

open scoped WithZero

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Transport the original local-field valuation through the pinned actual
ordered value-group equivalence. This retains its original valuation ring. -/
def localFieldNormalizedValuation : Valuation K ℤᵐ⁰ :=
  Valuation.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.monotone
    (ValuativeRel.valuation K)

/-- Every integer value, including the zero value of the multiplicative
value group, is attained by the original normalized local-field valuation. -/
theorem localFieldNormalizedValuation_surjective :
    Function.Surjective (localFieldNormalizedValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    ValuativeRel.valuation_surjective

/-- The actual integer order of a nonzero field element. The sign is chosen
so original valuation-ring elements have nonnegative order. -/
def localFieldUnitOrder : Additive Kˣ →+ ℤ where
  toFun u := -WithZero.log (localFieldNormalizedValuation K (Additive.toMul u).val)
  map_zero' := by simp
  map_add' u v := by
    change -WithZero.log (localFieldNormalizedValuation K
      ((Additive.toMul u).val * (Additive.toMul v).val)) = _
    rw [map_mul, WithZero.log_mul (by simp) (by simp), neg_add]

/-- Actual value-group surjectivity produces a field unit of each prescribed
integer order; no uniformizer or valuation-normalization hypothesis is supplied. -/
theorem localFieldUnitOrder_surjective : Function.Surjective (localFieldUnitOrder K) := by
  intro z
  obtain ⟨x, hx⟩ := localFieldNormalizedValuation_surjective K (WithZero.exp (-z))
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact (WithZero.exp_ne_zero (a := -z)) hx.symm
  refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
  change -WithZero.log (localFieldNormalizedValuation K x) = z
  rw [hx, WithZero.log_exp, neg_neg]

/-- The integer order detects precisely the original valuation-ring
inequality on the same original nonzero field value. -/
theorem localFieldUnitOrder_nonneg_iff (u : Kˣ) :
    0 ≤ localFieldUnitOrder K (Additive.ofMul u) ↔ ValuativeRel.valuation K u.val ≤ 1 := by
  change 0 ≤ -WithZero.log (localFieldNormalizedValuation K u.val) ↔ _
  rw [neg_nonneg]
  have hn : localFieldNormalizedValuation K u.val ≠ 0 := by simp
  rw [← WithZero.log_one, WithZero.log_le_log hn one_ne_zero]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
    (ValuativeRel.valuation K u.val) ≤ 1 ↔ _
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.le_iff_le

end
end Dubon2026
