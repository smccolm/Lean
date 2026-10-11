import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The actual local-field integer ring is the original integral closure -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The original extension integer ring is precisely the integral closure
of the original base integer ring in the original field. Finite generation is
proved from compactness; the actual DVR is integrally closed in its fraction field. -/
theorem localField_integer_isIntegralClosure : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  infer_instance

end
end Dubon2026
