import Dubon2026.SourceLaurentReindex
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Divisors

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form lower dimension bound -> regular differential realization.
This selects the original Laurent-series modular function field and its
literal j series. The analytic modularity and finite extension are assembled in
SourceOriginalDifferentialInjectivity. Regularity, geometric genus and
cusp-form realization remain separate proof obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_X0.lean, JFunction section.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries IntermediateField

open scoped PowerSeries.WithPiTopology
open PowerSeries

section JFunction

/-- The integral q series with the exact normalized weight-four Eisenstein coefficients. -/
def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

@[simp]
theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein4]

/-- The formal product of one minus each positive power of q. -/
def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

theorem constantCoeff_etaProd : PowerSeries.constantCoeff etaProd = 1 := by
  rw [etaProd]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]

/-- The twenty-fourth power of the original eta unit series. -/
def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24

theorem constantCoeff_dedekindEtaUnit : PowerSeries.constantCoeff dedekindEtaUnit = 1 := by
  rw [dedekindEtaUnit, map_pow, constantCoeff_etaProd, one_pow]

/-- The formal inverse with the proved unit constant coefficient. -/
def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1

theorem dedekindEtaUnit_mul_inv : dedekindEtaUnit * dedekindEtaUnitInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_dedekindEtaUnit]; rfl)

theorem constantCoeff_dedekindEtaUnitInv :
    PowerSeries.constantCoeff dedekindEtaUnitInv = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) dedekindEtaUnit_mul_inv
  rwa [map_mul, constantCoeff_dedekindEtaUnit, one_mul, map_one] at h

/-- The original integral numerator of the Laurent j series. -/
def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv

@[simp]
theorem constantCoeff_jNum : PowerSeries.constantCoeff jNum = 1 := by
  rw [jNum, map_mul, map_pow, constantCoeff_eisenstein4, constantCoeff_dedekindEtaUnitInv,
    one_pow, one_mul]

/-- The rational coefficient image of the original integral numerator. -/
def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)

@[simp]
theorem constantCoeff_jNumQ : PowerSeries.constantCoeff jNumQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, jNumQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  simp

/-- The original Laurent j series, with principal term q inverse. -/
def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ

theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

theorem jq_pow (n : ℕ) :
    jq ^ n = HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (jNumQ ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jq, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem coeff_jq_pow_self (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNumQ, one_pow]

theorem coeff_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jq ^ n).coeff m = 0 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

@[simp]
theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1 := by
  have h := coeff_jq_pow_self 1
  simpa using h

theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := by
  have h := coeff_jq_pow_of_lt (n := 1) (m := k) (by simpa using hk)
  simpa using h

theorem jq_ne_zero : jq ≠ 0 := fun h => by simpa [h] using coeff_jq_neg_one

end JFunction

end
end Dubon2026.SourceFunctionField
