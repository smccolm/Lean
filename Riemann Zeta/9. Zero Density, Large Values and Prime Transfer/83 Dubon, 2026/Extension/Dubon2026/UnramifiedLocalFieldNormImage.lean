import Dubon2026.UnramifiedLocalFieldNormOrder
import Dubon2026.UnramifiedLocalFieldZeroOrderNorm
import Dubon2026.LocalFieldNormOrderCriterion

/-! # The original norm image in a finite unramified local-field extension -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Original field-unit norm membership is equivalent to divisibility of
the original normalized order by the extension degree. The actual finite
unramified integer-ring structures discharge both inputs of the order criterion. -/
theorem unramifiedLocalField_mem_normRange_iff_order_dvd (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) := by
  exact localFieldUnit_mem_normRange_iff_order_dvd
    unramifiedLocalField_norm_order unramifiedLocalField_exists_norm_of_order_zero u

end
end Dubon2026
