import Dubon2026.SourceCurveIntegralExpressionOrders
import Dubon2026.SourceCurveDerivativeLowerOrder
import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> actual Gamma1 regular differential/cusp comparison.
The exact six/four/three integral expression forces a nonnegative local
differential order. Reuse the proved integral derivative coefficient and
uniformizer derivative lower bound; no upper j-ramification bound is needed
for this direction of the comparison.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem ordDifferential_nonneg_of_finite_expression
    (g J : F) (h1728 : (1728 : K) ≠ 0)
    (hu : 0 ≤ v.ord (g ^ 6 * J ^ 4 * (J - algebraMap K F 1728) ^ 3)) :
    0 ≤ v.ordDifferential (g • KaehlerDifferential.D K F J) := by

  by_cases hg : g = 0
  · subst hg; rw [zero_smul]; exact by simp [ordDifferential]
  by_cases hD : KaehlerDifferential.D K F J = 0
  · rw [hD, smul_zero]; exact by simp [ordDifferential]

  set c : F := algebraMap K F 1728 with hc_def
  have hc : c ≠ 0 := fun h => h1728 ((map_eq_zero_iff _ (algebraMap K F).injective).mp h)
  have hJ0 : J ≠ 0 := by rintro rfl; exact hD (map_zero _)
  have hDc : KaehlerDifferential.D K F (J - c) = KaehlerDifferential.D K F J := by
    rw [map_sub, hc_def, (KaehlerDifferential.D K F).map_algebraMap, sub_zero]
  have hJc : J - c ≠ 0 := by
    intro h0
    apply hD
    rw [← hDc, h0, map_zero]

  have hexp : 0 ≤ 6 * v.ord g + 4 * v.ord J + 3 * v.ord (J - c) := by
    have h := hu
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJc),
      v.ord_mul (pow_ne_zero _ hg) (pow_ne_zero _ hJ0), v.ord_natPow, v.ord_natPow,
      v.ord_natPow] at h
    push_cast at h
    linarith
  rw [v.ordDifferential_smul hg (RegularDifferentialsComparison.differentialCoeff_ne_zero hD v)]
  have hc0 : v.ord c = 0 := v.ord_algebraMap 1728
  have hnc0 : v.ord (-c) = 0 := by rw [v.ord_neg, hc0]

  have hA5 : v.ord J - 1 ≤ v.ordDifferential (KaehlerDifferential.D K F J) := v.ord_sub_one_le_ordDifferential_D hD
  have hA5c : v.ord (J - c) - 1 ≤ v.ordDifferential (KaehlerDifferential.D K F J) := by
    have h := v.ord_sub_one_le_ordDifferential_D (f := J - c) (by rw [hDc]; exact hD)
    rwa [hDc] at h
  rcases lt_trichotomy (v.ord J) 0 with hneg | hzero | hpos
  ·
    have h2 : v.ord (J - c) = v.ord J := by
      rw [sub_eq_add_neg, v.ord_add_eq_of_lt hJ0 (neg_ne_zero.mpr hc) (by rw [hnc0]; exact hneg)]
    omega
  ·
    have hA4 : 0 ≤ v.ordDifferential (KaehlerDifferential.D K F J) := v.ordDifferential_D_nonneg_of_mem (v.mem_of_ord_nonneg hzero.ge)
    rcases lt_or_ge (v.ord (J - c)) 0 with hneg' | hnn'
    · exfalso
      have h3 : v.ord (J - c + c) = v.ord (J - c) :=
        v.ord_add_eq_of_lt hJc hc (by rw [hc0]; exact hneg')
      rw [sub_add_cancel] at h3
      omega
    · omega
  ·
    have h2 : v.ord (J - c) = 0 := by
      rw [sub_eq_add_neg, add_comm, v.ord_add_eq_of_lt (neg_ne_zero.mpr hc) hJ0 (by rw [hnc0]; exact hpos), hnc0]
    omega

end
end Dubon2026.SourceCurve.Place
