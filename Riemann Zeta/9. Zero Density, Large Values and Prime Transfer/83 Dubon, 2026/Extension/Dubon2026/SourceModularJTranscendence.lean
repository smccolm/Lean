import Dubon2026.SourceModularJBaseChange
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form lower dimension bound -> regular differential realization.
This selects the original Laurent-series modular function field and its
literal j series. The analytic modularity and finite extension are assembled in
SourceOriginalDifferentialInjectivity. Regularity, geometric genus and
cusp-form realization remain separate proof obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_transcendental_jqModC.lean, principal-coefficient argument.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries IntermediateField

variable (K : Type*) [CommRing K]

theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

theorem coeff_jqModC_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

theorem coeff_jqModC_neg_one : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

theorem aeval_jqModC_eq_zero {p : Polynomial K} (hp : Polynomial.aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (Polynomial.aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single n]
    · rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_of_lt, mul_zero]
      omega
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

theorem transcendental_jqModC : Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => aeval_jqModC_eq_zero K hp

theorem jqModC_ne_zero [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have h1 : (jqModC K).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem order_jqModC [Nontrivial K] : (jqModC K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_jqModC_neg_one]
    exact one_ne_zero
  · by_contra hlt
    rw [not_le] at hlt
    refine HahnSeries.coeff_order_eq_zero.not.mpr (jqModC_ne_zero K) ?_
    have h := coeff_jqModC_pow_of_lt K (n := 1) (m := (jqModC K).order)
      (by simpa using hlt)
    simpa using h

end
end Dubon2026.SourceFunctionField
