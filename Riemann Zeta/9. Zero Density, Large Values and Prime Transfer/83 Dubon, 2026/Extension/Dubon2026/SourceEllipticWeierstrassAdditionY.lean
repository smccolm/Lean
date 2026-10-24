import Dubon2026.SourceEllipticWeierstrassAdditionX
import Dubon2026.SourceEllipticPeriodSlopeDerivative

/-! Derive the actual y-addition formula by differentiating the proved
x-formula and the actual secant slope. This avoids the separate upstream
y-defect and principal-part calculation. The resulting coordinate identities
serve the actual uniformization and DUB-17/18 odd-prime quotient product. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set WeierstrassCurve
open scoped PeriodPair Topology

theorem weierstrassP_add_eq_periodSlope (L : PeriodPair) {w z : ℂ}
    (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = periodSlope L w z ^ 2 - ℘[L] z - ℘[L] w := by
  rw [weierstrassP_add_eq_addX L hw h2w hz hzw hne, ← periodSlope_eq_slope L hne]
  simp [Affine.addX, periodCurve]

theorem derivWeierstrassP_add_eq_addY (L : PeriodPair) {w z : ℂ}
    (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice)
    (hz : z ∉ L.lattice) (hzw : z + w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w) / 2 = (periodCurve L).toAffine.addY (℘[L] z) (℘[L] w)
      (℘'[L] z / 2) ((periodCurve L).toAffine.slope
        (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2)) := by
  have hn := (L.analyticOnNhd_weierstrassP z hz).continuousAt.eventually_ne hne
  have hEq : (fun u => ℘[L] (u + w)) =ᶠ[𝓝 z]
      fun u => periodSlope L w u ^ 2 - ℘[L] u - ℘[L] w := by
    have hU : {u : ℂ | u + w ∉ L.lattice} ∈ 𝓝 z :=
      (L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)).mem_nhds hzw
    filter_upwards [hn, L.isClosed_lattice.isOpen_compl.mem_nhds hz, hU] with u hne' hu huw
    exact weierstrassP_add_eq_periodSlope L hw h2w hu huw hne'
  have hP : HasDerivAt ℘[L] (℘'[L] z) z :=
    L.deriv_weierstrassP ▸ (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hFun : HasDerivAt (fun u => periodSlope L w u ^ 2 - ℘[L] u - ℘[L] w)
      (2 * periodSlope L w z * (2 * ℘[L] z + ℘[L] w - periodSlope L w z ^ 2) - ℘'[L] z) z := by
    convert (((hasDerivAt_periodSlope L hz hw hne).pow 2).sub hP).sub_const (℘[L] w) using 1
    ring
  have hd : ℘'[L] (z + w) =
      2 * periodSlope L w z * (2 * ℘[L] z + ℘[L] w - periodSlope L w z ^ 2) - ℘'[L] z := by
    rw [← (hasDerivAt_weierstrassP_add L hzw).deriv, hEq.deriv_eq, hFun.deriv]
  rw [hd, ← periodSlope_eq_slope L hne, Affine.addY, Affine.negY, Affine.negAddY,
    Affine.addX]
  simp only [periodCurve]
  ring

end Dubon2026.SourceEllipticPeriod
