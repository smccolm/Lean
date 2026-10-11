import Dubon2026.LocalFieldUniformizerOrder
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Unramified.LocalRing

/-! # An original uniformizer remains a uniformizer in an unramified local extension -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Actual formal unramifiedness identifies the mapped original maximal
ideal, so the image of each original integer-ring uniformizer is irreducible. -/
theorem unramifiedLocalField_irreducible_algebraMap (q : 𝒪[K])
    (hq : Irreducible q) : Irreducible (algebraMap 𝒪[K] 𝒪[L] q) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := 𝒪[K]) (S := 𝒪[L]),
    (IsDiscreteValuationRing.irreducible_iff_uniformizer q).mp hq,
    Ideal.map_span, Set.image_singleton]

end
end Dubon2026
