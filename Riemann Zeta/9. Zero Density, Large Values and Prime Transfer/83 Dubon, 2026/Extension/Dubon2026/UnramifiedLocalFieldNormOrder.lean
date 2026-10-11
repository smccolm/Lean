import Dubon2026.LocalFieldIntegerUnitNorm
import Dubon2026.UnramifiedLocalFieldUniformizer

/-! # The degree formula for the original normalized order of an unramified norm -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]] [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- In the actual finite unramified integer-ring extension, the original
normalized order of the actual field norm is the extension degree times the
original normalized order. This follows from actual uniformizer factorization,
the original scalar norm formula, and actual norm localization on units. -/
theorem unramifiedLocalField_norm_order (v : Lˣ) :
    localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
      (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v) := by
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let π := Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)
  let j := Units.map (algebraMap K L).toMonoidHom
  let N := Units.map (Algebra.norm K (S := L))
  have hqL := unramifiedLocalField_irreducible_algebraMap (L := L) q hq
  obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power L
    (algebraMap 𝒪[K] 𝒪[L] q) hqL v
  have hπL : Units.mk0
      (algebraMap 𝒪[L] L (algebraMap 𝒪[K] 𝒪[L] q))
      (by simpa using hqL.ne_zero) = j π := by
    apply Units.ext
    rfl
  rw [hπL] at ha
  have hNπ : N (j π) = π ^ Module.finrank K L := by
    apply Units.ext
    exact Algebra.norm_algebraMap π.val
  have hπ : localFieldUnitOrder K (Additive.ofMul π) = 1 :=
    localFieldUnitOrder_irreducible K q hq
  have h := congrArg (fun x : Lˣ => localFieldUnitOrder K (Additive.ofMul (N x))) ha
  dsimp only at h
  rw [map_mul, map_zpow] at h
  change localFieldUnitOrder K (Additive.ofMul (N v)) = localFieldUnitOrder K
    (Additive.ofMul (N (Units.map (algebraMap 𝒪[L] L).toMonoidHom a)) +
      localFieldUnitOrder L (Additive.ofMul v) • Additive.ofMul (N (j π))) at h
  rw [map_add, map_zsmul, localField_norm_integer_unit_order_zero, hNπ] at h
  change localFieldUnitOrder K (Additive.ofMul (N v)) = 0 +
    localFieldUnitOrder L (Additive.ofMul v) •
      localFieldUnitOrder K (Module.finrank K L • Additive.ofMul π) at h
  rw [map_nsmul, hπ] at h
  simpa [N, nsmul_eq_mul, zsmul_eq_mul, mul_comm] using h

end
end Dubon2026
