import Dubon2026.UnramifiedLocalFractionFieldNorm
import Dubon2026.LocalFieldIntegerUnitOrderKernel
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Norm preimages of order-zero units in the actual unramified local fields -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- For the original finite unramified integer-ring extension, every actual
base-field unit of order zero has an actual field-norm preimage. Freeness,
adic completeness, finite residue field and norm compatibility are derived.
Finiteness and unramifiedness concern the original integer rings. -/
theorem unramifiedLocalField_exists_norm_of_order_zero (u : Kˣ)
    (hu : localFieldUnitOrder K (Additive.ofMul u) = 0) :
    ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'
  haveI : Finite (𝒪[K] ⧸ IsLocalRing.maximalIdeal 𝒪[K]) := inferInstanceAs (Finite 𝓀[K])
  obtain ⟨a, ha⟩ := (localFieldUnitOrder_eq_zero_iff_integer_unit K u).mp hu
  obtain ⟨b, hb⟩ := unramifiedLocal_exists_fraction_field_unit_norm
    (R := 𝒪[K]) (S := 𝒪[L]) (K := K) (L := L) a
  exact ⟨Units.map (algebraMap 𝒪[L] L).toMonoidHom b, hb.trans ha⟩

end
end Dubon2026
