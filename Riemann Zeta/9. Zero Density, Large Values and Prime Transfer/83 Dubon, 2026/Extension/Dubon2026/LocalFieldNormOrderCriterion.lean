import Dubon2026.LocalFieldNormalizedUnitOrder
import Mathlib.RingTheory.Norm.Basic

/-! # The actual field-unit norm image from its original normalized orders -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]

/-- The actual local-field unit norm image is detected by divisibility of
the original normalized integer order once the original degree formula and
norm surjectivity on order-zero units have been proved. These are displayed
narrower unramified inputs, not an assumed norm-image criterion. -/
theorem localFieldUnit_mem_normRange_iff_order_dvd
    (hnorm : ∀ v : Lˣ,
      localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
        (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v))
    (hzero : ∀ u : Kˣ, localFieldUnitOrder K (Additive.ofMul u) = 0 →
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u)
    (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨localFieldUnitOrder L (Additive.ofMul v), hnorm v⟩
  · rintro ⟨m, hm⟩
    obtain ⟨v, hv⟩ := localFieldUnitOrder_surjective L m
    let N := Units.map (Algebra.norm K (S := L))
    let w := u / N v.toMul
    have hw : localFieldUnitOrder K (Additive.ofMul w) = 0 := by
      change localFieldUnitOrder K (Additive.ofMul u - Additive.ofMul (N v.toMul)) = 0
      rw [map_sub, hnorm]
      change localFieldUnitOrder K (Additive.ofMul u) -
        (Module.finrank K L : ℤ) * localFieldUnitOrder L v = 0
      rw [hv, hm, sub_self]
    obtain ⟨a, ha⟩ := hzero w hw
    refine ⟨a * v.toMul, ?_⟩
    rw [map_mul, ha]
    change (u / N v.toMul) * N v.toMul = u
    exact div_mul_cancel _ _

end
end Dubon2026
