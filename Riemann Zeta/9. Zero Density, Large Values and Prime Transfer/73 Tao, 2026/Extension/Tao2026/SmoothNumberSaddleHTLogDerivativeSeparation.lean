import Tao2026.SmoothNumberSaddleHTContourEdgeWeighted
import Tao2026.SmoothNumberSaddleHTContourWidth
import GafniTao.SharpPerronPartialFraction

/-!
# Quantitative zero separation on the HT contour

The contour shift is asymptotically smaller than the native
Vinogradov--Korobov width by a power of `log y`.  This module spends half of
that width to obtain a genuine horizontal gap: the contour lies at least one
additional shift to the right of every zeta zero in the relevant rectangle.

The final theorem transports this gap to the normalized Landau disk used by
the frozen logarithmic-derivative machinery.  It is the denominator estimate
needed to replace good-height separation by zero-free-strip separation.
-/

open Complex Filter Set Topology Metric Finset
open RiemannZeta.GuthMaynard

namespace Tao2026

noncomputable section

/-- The asymptotic VK comparison has enough slack for twice the selected
contour shift, uniformly at the complete translated contour height. -/
theorem eventually_two_mul_smoothSaddleHTContourShift_le_vk_actualHeight
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεOne : ε < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
      2 * smoothSaddleHTContourShift y ε ≤ c /
        GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y ε) := by
  have hcHalf : 0 < c / 2 := by linarith
  filter_upwards
    [eventually_smoothSaddleHTContourShift_le_vk_actualHeight
      hcHalf hε hεOne] with y hy
  intro t ht
  have hraw := hy t ht
  calc
    2 * smoothSaddleHTContourShift y ε ≤
        2 * ((c / 2) /
          GafniTao.vinogradovKorobovDenominator
            (|t| + smoothSaddleHTContourHeight y ε)) := by
      gcongr
    _ = c / GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y ε) := by ring

/-- If twice `eta` fits inside a rectangle-uniform VK width, every zero in
that rectangle is more than `eta` away from any point with real part at
least `1-eta`. -/
theorem norm_sub_zero_gt_of_vinogradovKorobovRectangleZeroFree
    {c H eta T : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hHeight : H ≤ T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator T)
    {w rho : ℂ} (hwRe : 1 - eta ≤ w.re)
    (hrho : rho ∈ GafniTao.zeroSet 0 T) :
    eta < ‖w - rho‖ := by
  have hrhoRight := (hZeroFree hHeight).2.2 hrho
  have hre : eta < (w - rho).re := by
    simp only [sub_re]
    linarith
  have habs : eta < |(w - rho).re| := by
    rw [abs_of_pos (heta.trans hre)]
    exact hre
  exact habs.trans_le (Complex.abs_re_le_norm (w - rho))

/-- A zero from the frozen normalized Landau disk is quantitatively
separated from every physical point to the right of `1-eta`.  The displayed
factor `7/4` is exactly the affine Landau-map scale. -/
theorem sharpLandauCoord_zero_separation_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hSigma : 1 - eta ≤ sigma)
    {rho : ℂ} (hrho : rho ∈ GafniTao.sharpLandauZeroFinset T hT) :
    eta < (7 / 4 : ℝ) *
      ‖GafniTao.sharpLandauCoord T sigma R - rho‖ := by
  have hrhoSmall : rho ∈ GafniTao.SetOfZeros (24 / 25)
      (GafniTao.sharpLandauNormalized T) :=
    ((GafniTao.finiteSetOfZeros_mono (by norm_num : (24 / 25 : ℝ) < 1)
      (GafniTao.finite_sharpLandauNormalized_zeros hT)).mem_toFinset).mp hrho
  have hrhoUnit : rho ∈ GafniTao.SetOfZeros 1
      (GafniTao.sharpLandauNormalized T) :=
    ⟨hrhoSmall.1.trans (by norm_num), hrhoSmall.2⟩
  have hrhoPhysical := GafniTao.sharpLandauMap_mem_zeroSet hT hrhoUnit
  have hsep := norm_sub_zero_gt_of_vinogradovKorobovRectangleZeroFree
    hZeroFree hHeight heta hWidth
    (w := GafniTao.sharpLandauMap T
      (GafniTao.sharpLandauCoord T sigma R))
    (rho := GafniTao.sharpLandauMap T rho)
    (by rw [GafniTao.sharpLandauMap_coord]; simp; linarith) hrhoPhysical
  rw [GafniTao.sharpLandauMap_coord] at hsep
  have hdiff :
      ((sigma : ℂ) + (R : ℂ) * Complex.I) -
          GafniTao.sharpLandauMap T rho =
        (7 / 4 : ℝ) *
          (GafniTao.sharpLandauCoord T sigma R - rho) := by
    rw [← GafniTao.sharpLandauMap_coord T sigma R]
    unfold GafniTao.sharpLandauMap
    push_cast
    ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)] at hsep
  exact hsep

end

end Tao2026
