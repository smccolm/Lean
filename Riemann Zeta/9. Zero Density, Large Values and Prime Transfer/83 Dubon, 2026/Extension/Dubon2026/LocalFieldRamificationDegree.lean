import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! # The original local-field degree is ramification times residue degree -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The actual maximal ideals of the original integer rings give the
ramification index, and the original residue fields give the residue degree.
Their product is the degree of the original field extension. -/
theorem localField_ramification_mul_residue_degree :
    (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx (IsLocalRing.maximalIdeal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  have h := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (R := 𝒪[K]) (S := 𝒪[L]) K L
    (p := IsLocalRing.maximalIdeal 𝒪[K])
    (IsDiscreteValuationRing.not_a_field 𝒪[K])
  rw [Ideal.inertiaDeg_algebraMap] at h
  exact h

end
end Dubon2026
