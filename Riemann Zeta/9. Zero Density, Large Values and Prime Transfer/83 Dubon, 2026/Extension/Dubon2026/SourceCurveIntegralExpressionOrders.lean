import Dubon2026.SourceCurveCoordinateSupport
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> local
regularity. Reuse valuation-ring integral closure to turn the proved
coordinate integral equations into orders. The positive-M cusp expression
forces ord(Y) >= 1 - ord(j), exactly compensating the pole of D(j). -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_natPow (x : F) (n : ℕ) : v.ord (x ^ n) = (n : ℤ) * v.ord x := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_nonneg_of_integral_coordinate {j x : F}
    (hj : 0 ≤ v.ord j) (hx : IsIntegral (Algebra.adjoin K ({j} : Set F)) x) :
    0 ≤ v.ord x := by
  apply v.ord_nonneg_of_mem
  refine integralClosure_mem_of_base_mem v ?_
    (⟨x, hx⟩ : integralClosure (Algebra.adjoin K ({j} : Set F)) F)
  intro a
  change (a : F) ∈ v.toValuationSubring
  suffices h : ∀ z : F, z ∈ Algebra.adjoin K ({j} : Set F) →
      z ∈ v.toValuationSubring from h a a.2
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain rfl : z = j := hz
    exact v.mem_of_ord_nonneg hj
  | algebraMap c => exact v.algebraMap_mem' c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem cusp_coefficient_order_of_integral_expression [CharZero K]
    (M : ℕ) [NeZero M] (j y : F) (hy : y ≠ 0) (hj : v.ord j < 0)
    (hi : IsIntegral (Algebra.adjoin K ({j⁻¹} : Set F))
      (y ^ (2 * M) * j ^ (M + 1) * (j - algebraMap K F 1728) ^ M)) :
    1 - v.ord j ≤ v.ord y := by
  let c := algebraMap K F 1728
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hj
    exact lt_irrefl _ hj
  have hc : c ≠ 0 := by
    change algebraMap K F (1728 : K) ≠ 0
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr (by norm_num)
  have hnc : v.ord (-c) = 0 := by rw [v.ord_neg]; exact v.ord_algebraMap _
  have hsub : v.ord (j - c) = v.ord j := by
    rw [sub_eq_add_neg, v.ord_add_eq_of_lt hj0 (neg_ne_zero.mpr hc) (by rw [hnc]; exact hj)]
  have hsub0 : j - c ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hsub
    omega
  have hu := v.ord_nonneg_of_integral_coordinate
    (j := j⁻¹) (by rw [v.ord_inv]; omega) hi
  change 0 ≤ v.ord (y ^ (2 * M) * j ^ (M + 1) * (j - c) ^ M) at hu
  rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hy) (pow_ne_zero _ hj0))
      (pow_ne_zero _ hsub0),
    v.ord_mul (pow_ne_zero _ hy) (pow_ne_zero _ hj0),
    v.ord_natPow, v.ord_natPow, v.ord_natPow, hsub] at hu
  push_cast at hu
  have hM : (1 : ℤ) ≤ M := by exact_mod_cast NeZero.one_le
  by_contra hn
  have hny : v.ord y ≤ -v.ord j := by omega
  have hm := mul_le_mul_of_nonneg_left hny (show (0 : ℤ) ≤ M by omega)
  nlinarith

end
end Dubon2026.SourceCurve.Place
