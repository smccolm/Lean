import Dubon2026.LocalFieldIntegerUnitAction
import Dubon2026.LocalFieldUniformizerOrder

/-! # The original normalized integer order is Galois invariant -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- Actual local Galois automorphisms preserve the original normalized unit
order. The proof uses their genuine integer-ring restriction, preservation of
irreducible uniformizers and the proved original unit-times-uniformizer decomposition. -/
theorem localFieldUnitOrder_galois_invariant
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (σ : Gal(L/K)) (x : Lˣ) :
    localFieldUnitOrder L (Additive.ofMul (σ • x)) = localFieldUnitOrder L (Additive.ofMul x) := by
  letI := localFieldIntegerUnitMulDistribMulAction K L
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  let π := Units.mk0 (algebraMap 𝒪[L] L q) (by simpa using hq.ne_zero)
  let e := localFieldIntegerGaloisEquiv K L σ
  have hq' : Irreducible (e q) := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr hq
  have hσπ : σ • π = Units.mk0 (algebraMap 𝒪[L] L (e q)) (by simpa using hq'.ne_zero) := by
    apply Units.ext
    exact (localFieldIntegerGaloisEquiv_apply K L σ q).symm
  have hπ : localFieldUnitOrder L (Additive.ofMul (σ • π)) = 1 := by
    rw [hσπ]
    exact localFieldUnitOrder_irreducible L (e q) hq'
  let j := Units.map (algebraMap 𝒪[L] L).toMonoidHom
  obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power L q hq x
  have hz : localFieldUnitOrder L (Additive.ofMul (j (σ • a))) = 0 :=
    (localFieldUnitOrder_eq_zero_iff_integer_unit L _).mpr ⟨σ • a, rfl⟩
  have hsx : σ • x = j (σ • a) * (σ • π) ^ localFieldUnitOrder L (Additive.ofMul x) := by
    conv_lhs => rw [ha]
    rw [smul_mul', smul_zpow', ← localFieldIntegerUnit_inclusion_equivariant K L σ a]
  rw [hsx]
  change localFieldUnitOrder L (Additive.ofMul (j (σ • a)) +
    localFieldUnitOrder L (Additive.ofMul x) • Additive.ofMul (σ • π)) = _
  simp only [map_add, map_zsmul, hz, hπ, zero_add, zsmul_eq_mul, mul_one, Int.cast_id]

end
end Dubon2026
