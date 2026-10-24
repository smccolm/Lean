import Dubon2026.SourceEllipticWeierstrassDerivatives
import Dubon2026.SourceEllipticPeriodCurve

/-! A shorter route to the y-addition formula: differentiate the actual secant
slope and use the two Weierstrass differential equations. This replaces a
separate removable-singularity argument for the y-coordinate. It supplies
the period-point addition law required by the DUB-17/18 odd-prime product. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
open WeierstrassCurve
open scoped PeriodPair

/-- The actual secant slope between the two Weierstrass-function points. -/
def periodSlope (L : PeriodPair) (w z : ℂ) : ℂ :=
  (℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))

theorem periodSlope_eq_slope (L : PeriodPair) {w z : ℂ} (hne : ℘[L] z ≠ ℘[L] w) :
    periodSlope L w z = (periodCurve L).toAffine.slope
      (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) := by
  rw [Affine.slope_of_X_ne hne, periodSlope]
  field_simp

theorem hasDerivAt_periodSlope (L : PeriodPair) {w z : ℂ}
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    HasDerivAt (periodSlope L w)
      (2 * ℘[L] z + ℘[L] w - periodSlope L w z ^ 2) z := by
  have hP : HasDerivAt ℘[L] (℘'[L] z) z :=
    L.deriv_weierstrassP ▸ (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hD : HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt.congr_deriv
      (deriv_derivWeierstrassP L hz)
  have hOa := L.derivWeierstrassP_sq z hz
  have hOb := L.derivWeierstrassP_sq w hw
  have hr : (6 * ℘[L] z ^ 2 - L.g₂ / 2) * (2 * (℘[L] z - ℘[L] w)) -
      (℘'[L] z - ℘'[L] w) * (2 * ℘'[L] z) =
      (2 * (℘[L] z - ℘[L] w)) ^ 2 * (2 * ℘[L] z + ℘[L] w) -
        (℘'[L] z - ℘'[L] w) ^ 2 := by
    linear_combination -hOa + hOb
  have hd : 2 * (℘[L] z - ℘[L] w) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hne)
  apply ((hD.sub_const _).div ((hP.sub_const _).const_mul 2) hd).congr_deriv
  rw [hr]
  rw [periodSlope, div_pow, sub_div, mul_div_cancel_left₀ _ (pow_ne_zero 2 hd)]

end
end Dubon2026.SourceEllipticPeriod
