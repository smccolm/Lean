import Dubon2026.SourceOriginalRegularCuspOrders
import Dubon2026.SourceCurveChartIntegralCriterion

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay.
Original regularity proves the precise inverse-j integrality relation used
to control the quotient at every cusp. The exponent is the actual proved
degree psi(N), and each local condition is discharged from the actual
canonical divisor, exceptional multiplicity and cusp-width bounds.
The required exponent combination is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar.
Only the inverse-j half is needed: finite analytic regularity is already proved.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

theorem original_regular_inverse_j_integral (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({(jOver N ℂ)⁻¹} : Set (modularFunctionFieldOver N ℂ)))
      (x ^ (2 * SourceLevelProjective.dedekindPsi N) *
        jOver N ℂ ^ (SourceLevelProjective.dedekindPsi N + 1) *
        (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) ^
          SourceLevelProjective.dedekindPsi N) := by
  have hj0 : jOver N ℂ ≠ 0 := by
    intro he
    exact transcendental_jOver N ℂ (he ▸ isAlgebraic_zero)
  have hs0 : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728 ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jOver N ℂ) 1728
  have ht : Transcendental ℂ (jOver N ℂ)⁻¹ :=
    fun h => transcendental_jOver N ℂ (IsAlgebraic.inv_iff.mp h)
  haveI := finiteDimensional_original_over_transcendental N ℂ ht
  apply isIntegral_adjoin_of_nonnegative_orders _ ht
  intro v hv
  rw [v.ord_inv] at hv
  have hj : v.ord (jOver N ℂ) ≤ 0 := by omega
  have hp : ∀ (f : modularFunctionFieldOver N ℂ) (n : ℕ), v.ord (f ^ n) = n * v.ord f := by
    intro f n
    simpa only [zpow_natCast] using v.ord_zpow f (n : ℤ)
  rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hj0)) (pow_ne_zero _ hs0),
    v.ord_mul (pow_ne_zero _ hx) (pow_ne_zero _ hj0), hp, hp, hp]
  push_cast
  have hM : (0 : ℤ) ≤ SourceLevelProjective.dedekindPsi N := Int.natCast_nonneg _
  have hb := original_regular_coefficient_canonical_bound N x hx hreg v
  rcases hj.lt_or_eq with hjneg | hjzero
  · rw [original_jCanonical_at_pole N ℂ v hjneg] at hb
    have hw := original_j_pole_order_le_psi N v hjneg
    have hconst : -(algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) ≠ 0 := by
      rw [neg_ne_zero, map_ne_zero]
      norm_num
    have hs : v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) =
        v.ord (jOver N ℂ) := by
      rw [sub_eq_add_neg]
      apply v.ord_add_eq_of_lt hj0 hconst
      rwa [v.ord_neg, v.ord_algebraMap]
    rw [hs]
    nlinarith [mul_nonneg hM hb]
  · have hsnonneg : 0 ≤ v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) :=
      v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg (by omega)) (v.algebraMap_mem' 1728))
    rcases hsnonneg.lt_or_eq with hspos | hszero
    · rw [original_jCanonical_at_value N ℂ v 1728 hspos] at hb
      have hsbound := original_j_1728_order_le_two N v hspos
      rw [hjzero]
      nlinarith [mul_nonneg hM hb, mul_nonneg hM (sub_nonneg.mpr hsbound)]
    · have hz := original_jCanonical_eq_zero_off_exceptional N v (by omega) (by omega) (by omega)
      rw [hz, add_zero] at hb
      rw [hjzero, ← hszero]
      nlinarith

end
end Dubon2026.SourceFunctionField
