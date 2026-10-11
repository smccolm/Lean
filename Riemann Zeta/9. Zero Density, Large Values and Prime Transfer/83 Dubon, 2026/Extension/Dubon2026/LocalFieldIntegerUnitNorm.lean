import Dubon2026.UnramifiedLocalFractionFieldNorm
import Dubon2026.LocalFieldIntegerUnitOrderKernel
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Original field norms of actual integer-ring units -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel nonZeroDivisors

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- The original field norm of an actual integer-ring unit is the image
of its original ring-unit norm. This is the actual localization identity. -/
theorem localField_norm_integer_unit (a : 𝒪[L]ˣ) :
    Units.map (Algebra.norm K (S := L))
      (Units.map (algebraMap 𝒪[L] L).toMonoidHom a) =
    Units.map (algebraMap 𝒪[K] K).toMonoidHom
      (Units.map (Algebra.norm 𝒪[K] (S := 𝒪[L])) a) := by
  haveI : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'
  apply Units.ext
  exact Algebra.norm_localization 𝒪[K] 𝒪[K]⁰ a.val

/-- Actual integer-ring units have field norms of original normalized order
zero, without an unramifiedness hypothesis. -/
theorem localField_norm_integer_unit_order_zero (a : 𝒪[L]ˣ) :
    localFieldUnitOrder K (Additive.ofMul
      (Units.map (Algebra.norm K (S := L))
        (Units.map (algebraMap 𝒪[L] L).toMonoidHom a))) = 0 := by
  rw [localField_norm_integer_unit]
  exact (localFieldUnitOrder_eq_zero_iff_integer_unit K _).mpr ⟨_, rfl⟩

end
end Dubon2026
