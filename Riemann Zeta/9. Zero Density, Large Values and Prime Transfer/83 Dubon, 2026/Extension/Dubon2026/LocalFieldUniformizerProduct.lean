import Dubon2026.LocalFieldUniformizerOrder
import Dubon2026.FiniteGeneratedAbelianPowerIndex

/-! # Actual uniformizer product and its power-index factor

The existing original normalized valuation and integer-unit decomposition
give the one free integer direction in the finite-place power index required
by DUB-17. No new valuation or local field is substituted.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (q : 𝒪[K]) (hq : Irreducible q)

/-- The original uniformizer and integer-unit inclusion define the actual
additive product map on the multiplicative field units. -/
def localFieldUniformizerProductMap : ℤ × Additive 𝒪[K]ˣ →+ Additive Kˣ where
  toFun x := x.1 • Additive.ofMul
    (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)) +
      (Units.map (algebraMap 𝒪[K] K).toMonoidHom).toAdditive x.2
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul, map_add]
    abel

/-- The actual normalized order reads off precisely the uniformizer exponent. -/
theorem localFieldUniformizerProductMap_order (x : ℤ × Additive 𝒪[K]ˣ) :
    localFieldUnitOrder K (localFieldUniformizerProductMap K q hq x) = x.1 := by
  have hi : localFieldUnitOrder K
      ((Units.map (algebraMap 𝒪[K] K).toMonoidHom).toAdditive x.2) = 0 :=
    (localFieldUnitOrder_eq_zero_iff_integer_unit K _).mpr ⟨x.2.toMul, rfl⟩
  change localFieldUnitOrder K (x.1 • _ + _) = _
  rw [map_add, map_zsmul, localFieldUnitOrder_irreducible K q hq, hi, add_zero]
  exact mul_one x.1

/-- The proved integer-unit factorization and normalized order make the
actual uniformizer product map bijective. -/
theorem localFieldUniformizerProductMap_bijective :
    Function.Bijective (localFieldUniformizerProductMap K q hq) := by
  constructor
  · intro x y h
    have he : x.1 = y.1 := by
      simpa only [localFieldUniformizerProductMap_order] using congrArg (localFieldUnitOrder K) h
    apply Prod.ext he
    have hc : (Units.map (algebraMap 𝒪[K] K).toMonoidHom).toAdditive x.2 =
        (Units.map (algebraMap 𝒪[K] K).toMonoidHom).toAdditive y.2 := by
      let π : Additive Kˣ := Additive.ofMul
        (Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero))
      change x.1 • π + _ = y.1 • π + _ at h
      rw [he] at h
      exact add_left_cancel h
    change x.2.toMul = y.2.toMul
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : Additive Kˣ => (z.toMul : K)) hc
  · intro u
    obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power K q hq u.toMul
    refine ⟨(localFieldUnitOrder K u, Additive.ofMul a), ?_⟩
    change _ * _ = u.toMul
    exact (mul_comm _ _).trans ha.symm

/-- The original field-unit group is the actual integer-unit group together
with the original normalized integer valuation direction. -/
def localFieldUniformizerProductEquiv : ℤ × Additive 𝒪[K]ˣ ≃+ Additive Kˣ :=
  AddEquiv.ofBijective (localFieldUniformizerProductMap K q hq)
    (localFieldUniformizerProductMap_bijective K q hq)

omit q hq in
/-- The actual field-unit power index is the exponent times the original
integer-unit power index. -/
theorem localField_unitPower_index_uniformizer_factor (n : ℕ) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let e := localFieldUniformizerProductEquiv K π hπ
  have h := AddSubgroup.index_map_equiv
    (nsmulAddMonoidHom (α := ℤ × Additive 𝒪[K]ˣ) n).range e
  rw [AddEquiv.map_range_nsmulAddMonoidHom, nsmul_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul ℤ n] at h
  simpa only [Module.finrank_self, pow_one] using h

end
end Dubon2026
