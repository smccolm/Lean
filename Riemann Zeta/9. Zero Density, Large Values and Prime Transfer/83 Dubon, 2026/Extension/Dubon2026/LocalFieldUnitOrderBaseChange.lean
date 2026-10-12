import Dubon2026.LocalFieldRamificationDegree
import Dubon2026.LocalFieldUniformizerOrder

/-! # Original normalized orders scale by the actual ramification index -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

/-- The order of the actual image of an original base uniformizer is
the genuine ramification index of the original maximal ideals. -/
theorem localFieldUnitOrder_base_uniformizer (q : 𝒪[K]) (hq : Irreducible q) :
    localFieldUnitOrder L (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)))) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hx : algebraMap 𝒪[K] 𝒪[L] q ≠ 0 := by
    intro h
    apply hq.ne_zero
    apply FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L]
    simpa only [map_zero] using h
  obtain ⟨n, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hp
  have hmap : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) =
      IsLocalRing.maximalIdeal 𝒪[L] ^ n := by
    rw [hq.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, ha,
      Ideal.span_singleton_mul_left_unit a.isUnit, hp.maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have he : (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
      (IsLocalRing.maximalIdeal 𝒪[L]) = n := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field 𝒪[K]))
      inferInstance, hmap, multiplicity_pow_self
      (IsDiscreteValuationRing.not_a_field 𝒪[L])
      (Ideal.isUnit_iff.not.mpr (Ideal.IsMaximal.ne_top inferInstance))]
  let π := Units.mk0 (algebraMap 𝒪[L] L p) (by simpa using hp.ne_zero)
  have hu : Units.map (algebraMap K L).toMonoidHom
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)) =
      Units.map (algebraMap 𝒪[L] L).toMonoidHom a * π ^ n := by
    apply Units.ext
    change algebraMap K L (algebraMap 𝒪[K] K q) =
      algebraMap 𝒪[L] L a.val * (algebraMap 𝒪[L] L p) ^ n
    rw [← IsScalarTower.algebraMap_apply 𝒪[K] K L,
      IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, ha, map_mul, map_pow]
  rw [hu, he]
  change localFieldUnitOrder L (Additive.ofMul
    (Units.map (algebraMap 𝒪[L] L).toMonoidHom a) + n • Additive.ofMul π) = _
  rw [map_add, map_nsmul,
    (localFieldUnitOrder_eq_zero_iff_integer_unit L _).mpr ⟨a, rfl⟩,
    localFieldUnitOrder_irreducible L p hp, zero_add, nsmul_eq_mul, mul_one]

/-- On every actual base-field unit, the original normalized extension
order equals the original base order times the actual ramification index. -/
theorem localFieldUnitOrder_algebraMap (u : Kˣ) :
    localFieldUnitOrder L (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u)) =
      ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
        (IsLocalRing.maximalIdeal 𝒪[L]) : ℤ) * localFieldUnitOrder K (Additive.ofMul u) := by
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power K q hq u
  let j := Units.map (algebraMap K L).toMonoidHom
  have hunit : j (Units.map (algebraMap 𝒪[K] K).toMonoidHom a) =
      Units.map (algebraMap 𝒪[L] L).toMonoidHom
        (Units.map (algebraMap 𝒪[K] 𝒪[L]).toMonoidHom a) := by
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply 𝒪[K] K L a.val).symm.trans
      (IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L a.val)
  have hz : localFieldUnitOrder L (Additive.ofMul
      (j (Units.map (algebraMap 𝒪[K] K).toMonoidHom a))) = 0 := by
    rw [hunit]
    exact (localFieldUnitOrder_eq_zero_iff_integer_unit L _).mpr ⟨_, rfl⟩
  have h := congrArg (fun x : Kˣ => localFieldUnitOrder L (Additive.ofMul (j x))) ha
  dsimp only at h
  rw [map_mul, map_zpow] at h
  change localFieldUnitOrder L (Additive.ofMul (j u)) =
    localFieldUnitOrder L (Additive.ofMul
      (j (Units.map (algebraMap 𝒪[K] K).toMonoidHom a)) +
      localFieldUnitOrder K (Additive.ofMul u) • Additive.ofMul
        (j (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)))) at h
  rw [map_add, map_zsmul, hz, zero_add,
    localFieldUnitOrder_base_uniformizer K L q hq, zsmul_eq_mul, mul_comm] at h
  exact h

end
end Dubon2026
