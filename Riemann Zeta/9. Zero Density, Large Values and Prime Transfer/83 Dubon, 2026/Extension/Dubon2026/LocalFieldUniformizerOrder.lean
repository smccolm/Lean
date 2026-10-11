import Dubon2026.LocalFieldIntegerUnitOrderKernel

/-! # The normalized order of an actual integer-ring uniformizer -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- An irreducible of the original integer ring has normalized order one.
The normalization follows from surjectivity of the actual integer order,
not from an assumed value of a chosen uniformizer. -/
theorem localFieldUnitOrder_irreducible (q : 𝒪[K]) (hq : Irreducible q) :
    localFieldUnitOrder K (Additive.ofMul
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero))) = 1 := by
  let π := Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)
  have hπ : 0 ≤ localFieldUnitOrder K (Additive.ofMul π) :=
    (localFieldUnitOrder_nonneg_iff K π).mpr q.property
  obtain ⟨w, hw⟩ := localFieldUnitOrder_surjective K 1
  have hwv : ValuativeRel.valuation K w.toMul.val ≤ 1 :=
    (localFieldUnitOrder_nonneg_iff K w.toMul).mp (by simp [hw])
  let x : 𝒪[K] := ⟨w.toMul.val, hwv⟩
  have hx : x ≠ 0 := by
    intro h
    exact w.toMul.ne_zero (congrArg Subtype.val h)
  obtain ⟨n, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hq
  have he : w.toMul = Units.map (algebraMap 𝒪[K] K).toMonoidHom a * π ^ n := by
    apply Units.ext
    exact congrArg (algebraMap 𝒪[K] K) ha
  have haz : localFieldUnitOrder K
      (Additive.ofMul (Units.map (algebraMap 𝒪[K] K).toMonoidHom a)) = 0 :=
    (localFieldUnitOrder_eq_zero_iff_integer_unit K _).mpr ⟨a, rfl⟩
  have hone : (n : ℤ) * localFieldUnitOrder K (Additive.ofMul π) = 1 := by
    have h := congrArg (fun u : Kˣ => localFieldUnitOrder K (Additive.ofMul u)) he
    change localFieldUnitOrder K w = localFieldUnitOrder K
      (Additive.ofMul (Units.map (algebraMap 𝒪[K] K).toMonoidHom a) +
        n • Additive.ofMul π) at h
    rw [map_add, map_nsmul, haz, hw, zero_add] at h
    simpa only [nsmul_eq_mul] using h.symm
  have hn : 1 ≤ (n : ℤ) := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp [hn0] at hone
  have hh := mul_nonneg (show 0 ≤ (n : ℤ) - 1 by omega) hπ
  change localFieldUnitOrder K (Additive.ofMul π) = 1
  nlinarith

/-- Every original field unit is the product of an actual integer-ring
unit and the actual uniformizer to its normalized integer order. -/
theorem localFieldUnit_eq_integer_unit_mul_order_power (q : 𝒪[K])
    (hq : Irreducible q) (x : Kˣ) :
    ∃ a : 𝒪[K]ˣ, x = Units.map (algebraMap 𝒪[K] K).toMonoidHom a *
      (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)) ^
        (localFieldUnitOrder K (Additive.ofMul x)) := by
  let π := Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)
  obtain ⟨n, a, ha⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hq x.ne_zero
  have he : x = Units.map (algebraMap 𝒪[K] K).toMonoidHom a * π ^ n := by
    apply Units.ext
    simpa [Units.smul_def, Algebra.smul_def, π] using ha
  have haz : localFieldUnitOrder K
      (Additive.ofMul (Units.map (algebraMap 𝒪[K] K).toMonoidHom a)) = 0 :=
    (localFieldUnitOrder_eq_zero_iff_integer_unit K _).mpr ⟨a, rfl⟩
  have hn : localFieldUnitOrder K (Additive.ofMul x) = n := by
    have h := congrArg (fun u : Kˣ => localFieldUnitOrder K (Additive.ofMul u)) he
    change localFieldUnitOrder K (Additive.ofMul x) = localFieldUnitOrder K
      (Additive.ofMul (Units.map (algebraMap 𝒪[K] K).toMonoidHom a) +
        n • Additive.ofMul π) at h
    rw [map_add, map_zsmul, haz, zero_add] at h
    simpa only [π, localFieldUnitOrder_irreducible K q hq, zsmul_eq_mul, mul_one] using h
  exact ⟨a, hn.symm ▸ he⟩

end
end Dubon2026
