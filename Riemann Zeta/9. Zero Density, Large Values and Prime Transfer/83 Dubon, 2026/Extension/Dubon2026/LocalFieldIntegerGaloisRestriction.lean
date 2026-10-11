import Dubon2026.LocalFieldIntegerIntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! # Actual field automorphisms restrict to the original local integer rings -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- Actual field automorphisms and actual integer-ring algebra automorphisms
are equivalent. Both finite-dimensionality and the original integral-closure
structure are derived from actual local-field integer-ring compactness. -/
def localFieldIntegerGaloisEquiv : Gal(L/K) ≃* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  exact galRestrict 𝒪[K] K L 𝒪[L]

/-- The actual restriction retains the literal action on the original
field value of every original integer-ring element. -/
theorem localFieldIntegerGaloisEquiv_apply (g : Gal(L/K)) (x : 𝒪[L]) :
    algebraMap 𝒪[L] L (localFieldIntegerGaloisEquiv K L g x) =
      g (algebraMap 𝒪[L] L x) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  exact algebraMap_galRestrict_apply 𝒪[K] g x

end
end Dubon2026
