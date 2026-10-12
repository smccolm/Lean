import Dubon2026.NormedFieldUnitPowerOpen
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.LocalFieldOpenSmallUnits
import Dubon2026.LocalFieldUniformizerOrder

/-! # Finiteness of original local units modulo powers

The existing compatible norm, compact integer-unit quotient and actual
uniformizer decomposition supply the finiteness needed for Kummer H1.
-/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Actual field-unit nth powers are open in the original local topology when
n is nonzero in the original field. The norm is constructed without changing it. -/
theorem localField_unitPower_range_isOpen (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  exact normedField_unitPower_range_isOpen K n hn

/-- The original base-field units modulo their actual nth powers are finite.
Compact integer units supply one finite factor; the original uniformizer has
order dividing n in the quotient and supplies the remaining finite factor. -/
theorem localField_unitPower_quotient_finite (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  let U := (powMonoidHom n : Kˣ →* Kˣ).range
  let i := Units.map (algebraMap 𝒪[K] K).toMonoidHom
  let V := U.comap i
  haveI : Finite (𝒪[K]ˣ ⧸ V) :=
    localField_integer_unit_quotient_finite K U (localField_unitPower_range_isOpen K n hn)
  let j : 𝒪[K]ˣ ⧸ V →* Kˣ ⧸ U := QuotientGroup.map V U i le_rfl
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let π := Units.mk0 (algebraMap 𝒪[K] K q) (by simpa using hq.ne_zero)
  let πQ := QuotientGroup.mk' U π
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (h ▸ Nat.cast_zero)
  have hp : πQ ^ n = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (π ^ n)).mpr ⟨π, rfl⟩
  have hπ : IsOfFinOrder πQ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn0, hp⟩
  haveI : Finite (Subgroup.zpowers πQ) :=
    Finite.of_equiv (Fin (orderOf πQ)) (finEquivZPowers hπ)
  let f : (𝒪[K]ˣ ⧸ V) × Subgroup.zpowers πQ → Kˣ ⧸ U := fun z => j z.1 * z.2.val
  apply Finite.of_surjective f
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power K q hq x
    let k := localFieldUnitOrder K (Additive.ofMul x)
    refine ⟨(QuotientGroup.mk' V a, ⟨πQ ^ k, Subgroup.zpow_mem_zpowers πQ k⟩), ?_⟩
    change QuotientGroup.mk' U (i a) * (QuotientGroup.mk' U π) ^ k = QuotientGroup.mk' U x
    calc
      _ = QuotientGroup.mk' U (i a) * QuotientGroup.mk' U (π ^ k) :=
        congrArg (fun z => QuotientGroup.mk' U (i a) * z)
          (map_zpow (QuotientGroup.mk' U) π k).symm
      _ = QuotientGroup.mk' U (i a * π ^ k) := (map_mul (QuotientGroup.mk' U) _ _).symm
      _ = _ := congrArg (QuotientGroup.mk' U) ha.symm

end
end Dubon2026
