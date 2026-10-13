import Dubon2026.LocalFieldBallScalarQuotient
import Dubon2026.NormedFieldSmallUnitPowerImage
import Dubon2026.FiniteIndexEndomorphismKernel
import Dubon2026.SubringUnitSubgroupEquiv
import Dubon2026.LocalFieldOpenSmallUnits

/-! # Exact power index in the actual original local integer units

The inverse function theorem gives an actual small ball with injective power
map. Its image and the existing difference map identify its relative index
with the original integer ring modulo the exponent. The finite-index kernel
formula then gives the full integer-unit power index for DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- The original local-field NontriviallyNormedField structure used for this calculation. -/
local instance localFieldIntegerUnitPowerIndexNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- The original local-field IsUltrametricDist structure used for this calculation. -/
local instance localFieldIntegerUnitPowerIndexUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
/-- The original local-field CompleteSpace structure used for this calculation. -/
local instance localFieldIntegerUnitPowerIndexComplete : CompleteSpace K := localFieldOriginalNorm_complete K

/-- The original local integer-unit power index is its actual root-kernel
cardinality times the actual integer scalar-quotient cardinality. -/
theorem localField_integerUnit_power_index (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range) =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker *
        Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K])) := by
  obtain ⟨r, hr0, hr1, hsmall⟩ := normedField_exists_small_unit_power_image K n hn
  obtain ⟨a, ha0, har⟩ := NormedField.exists_norm_lt K (lt_min hr0 (norm_pos_iff.mpr hn))
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  have har' : ‖a‖ ≤ r := (lt_min_iff.mp har).1.le
  have han : ‖a‖ ≤ ‖(n : K)‖ := (lt_min_iff.mp har).2.le
  have ha1 : ‖a‖ < 1 := har'.trans_lt hr1
  have hna0 : 0 < ‖(n : K)‖ * ‖a‖ := mul_pos (norm_pos_iff.mpr hn) ha0
  have hna1 : ‖(n : K)‖ * ‖a‖ < 1 :=
    (mul_le_of_le_one_left ha0.le (IsUltrametricDist.norm_natCast_le_one K n)).trans_lt ha1
  let U := normedFieldSmallUnitSubgroup K ‖a‖ ha0.le ha1
  let V := normedFieldSmallUnitSubgroup K (‖(n : K)‖ * ‖a‖) hna0.le hna1
  let i := Units.map (algebraMap 𝒪[K] K).toMonoidHom
  let H := U.comap i
  let f := (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ)
  let F := (powMonoidHom n : Kˣ →* Kˣ)
  have hi : Function.Injective i := by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun u : Kˣ => (u : K)) h
  have hIntegral : ∀ u ∈ U, (u : K) ∈ (ValuativeRel.valuation K).integer := by
    intro u hu
    apply (localFieldOriginalNorm_integer_iff K u).mpr
    exact (normedField_norm_eq_one_of_sub_lt K (hu.trans_lt ha1)).le
  let e := subringUnitSubgroupEquiv (ValuativeRel.valuation K).integer U hIntegral
  have hHU : H.map i = U := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hu
      obtain ⟨x, hx⟩ := e.surjective ⟨u, hu⟩
      exact ⟨x, x.property, congrArg (fun z : U => (z : Kˣ)) hx⟩
  have hp : U.map F = V ∧ U ⊓ F.ker = ⊥ := hsmall ‖a‖ ha0 har'
  have hVU : V ≤ U := by
    intro u hu
    exact hu.trans (mul_le_of_le_one_left ha0.le (IsUltrametricDist.norm_natCast_le_one K n))
  have hcomm : i.comp f = F.comp i := by
    apply MonoidHom.ext
    intro x
    exact map_pow i x n
  have him : (H.map f).map i = V := by
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hHU, hp.1]
  have hstable : H.map f ≤ H := by
    rintro x ⟨y, hy, rfl⟩
    change i (f y) ∈ U
    rw [show i (f y) = F (i y) from DFunLike.congr_fun hcomm y]
    exact hVU (hp.1 ▸ Subgroup.mem_map.mpr ⟨i y, hy, rfl⟩)
  have hker : H ⊓ f.ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply hi
    rw [map_one]
    have hm : i x ∈ U ⊓ F.ker := by
      refine ⟨hx.1, ?_⟩
      change F (i x) = 1
      have hc : i (f x) = F (i x) := DFunLike.congr_fun hcomm x
      rw [← hc, show f x = 1 from hx.2, map_one]
    exact Subgroup.mem_bot.mp (hp.2 ▸ hm)
  haveI : Finite (𝒪[K]ˣ ⧸ H) := localField_integer_unit_quotient_finite K U
    (normedFieldSmallUnitSubgroup_isOpen K ‖a‖ ha0 ha1)
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hrel : (H.map f).relIndex H = V.relIndex U := by
    rw [← Subgroup.relIndex_map_map_of_injective (H.map f) H hi, him, hHU]
  change f.range.index = _
  rw [endomorphism_index_of_small_subgroup f H hstable hker, hrel]
  congr 1
  rw [normedFieldSmallUnit_relativeIndex K ‖a‖ (‖(n : K)‖ * ‖a‖)
    ha0 hna0 ha1 (mul_le_mul_of_nonneg_right han ha0.le) hna1]
  have hnI : (n : 𝒪[K]) ≠ 0 := by
    intro h
    apply hn
    calc
      (n : K) = algebraMap 𝒪[K] K (n : 𝒪[K]) := (map_natCast _ _).symm
      _ = 0 := by rw [h, map_zero]
  simpa only [norm_mul] using localFieldBallScalarQuotient_card K a ha (n : 𝒪[K]) hnI

end
end Dubon2026
