import Dubon2026.LocalFieldNormalizedUnitOrder

/-! # The kernel of the original normalized order is the image of the actual integer-ring units -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel WithZero

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Zero original integer order is exactly valuation one for the original
canonical valuation, with no alternative value-group normalization. -/
theorem localFieldUnitOrder_eq_zero_iff (u : Kˣ) :
    localFieldUnitOrder K (Additive.ofMul u) = 0 ↔ ValuativeRel.valuation K u.val = 1 := by
  change -WithZero.log (localFieldNormalizedValuation K u.val) = 0 ↔ _
  rw [neg_eq_zero]
  have hn : localFieldNormalizedValuation K u.val ≠ 0 := by simp
  constructor
  · intro h
    have he := congrArg WithZero.exp h
    rw [WithZero.exp_log hn, WithZero.exp_zero] at he
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (ValuativeRel.valuation K u.val) = 1 at he
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
    exact he.trans (map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm
  · intro h
    change WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (ValuativeRel.valuation K u.val)) = 0
    rw [h, map_one, WithZero.log_one]

/-- Every original field unit of normalized order zero comes from a
genuine unit of the original local-field integer ring, and conversely. -/
theorem localFieldUnitOrder_eq_zero_iff_integer_unit (u : Kˣ) :
    localFieldUnitOrder K (Additive.ofMul u) = 0 ↔
      ∃ a : 𝒪[K]ˣ, Units.map (algebraMap 𝒪[K] K).toMonoidHom a = u := by
  rw [localFieldUnitOrder_eq_zero_iff]
  constructor
  · intro hu
    let x : 𝒪[K] := ⟨u.val, hu.le⟩
    have hx : IsUnit x :=
      (Valuation.integer.integers (ValuativeRel.valuation K)).isUnit_of_one' hu
    refine ⟨hx.unit, ?_⟩
    apply Units.ext
    change algebraMap 𝒪[K] K hx.unit.val = u.val
    rw [hx.unit_spec]
    rfl
  · rintro ⟨a, rfl⟩
    exact (Valuation.integer.integers (ValuativeRel.valuation K)).valuation_unit a

end
end Dubon2026
