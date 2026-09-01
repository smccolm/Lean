import GafniTao.FordLocalCotangentLower

/-!
# The local-disk contribution to Ford's detector

This file inserts the actual multiplicity-weighted local disk into the exact
shifted detector.  Every member contributes at most a fixed negative amount
`-c/R`; summing gives the required coercive term involving Ford's `N(t,R)`.
-/

open Complex Finset Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordLocalNormalizedDisplacement
    (t R : ℝ) (rho : ℂ) : ℂ :=
  (fordShiftedDetectorCenter
      (1 + (6421 / 10000 : ℝ) * R) t - rho) / (R : ℂ)

theorem fordLocalNormalizedDisplacement_mem_region
    {t R : ℝ} (hR : 0 < R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    fordLocalNormalizedDisplacement t R rho ∈ fordLocalCotRegion := by
  have hd := mem_fordLocalDiskZeros_data hrho
  have hreNorm : |1 - rho.re| ≤ R := hd.2.2.2.1
  have himNorm : |t - rho.im| ≤ R := hd.2.2.2.2
  have hreAbs := abs_le.mp hreNorm
  have hzre : (fordLocalNormalizedDisplacement t R rho).re =
      (6421 / 10000 : ℝ) + (1 - rho.re) / R := by
    unfold fordLocalNormalizedDisplacement fordShiftedDetectorCenter
    simp [div_re]
    field_simp
    ring
  have hzim : (fordLocalNormalizedDisplacement t R rho).im =
      (t - rho.im) / R := by
    unfold fordLocalNormalizedDisplacement fordShiftedDetectorCenter
    simp [div_im]
    field_simp [hR.ne']
  rw [fordLocalCotRegion, mem_reProdIm]
  constructor
  · rw [hzre]
    constructor
    · have : 0 ≤ (1 - rho.re) / R :=
        div_nonneg (by linarith [hd.2.2.1]) hR.le
      linarith
    · have hquot : (1 - rho.re) / R ≤ 1 := by
        rw [div_le_one hR]
        exact hreAbs.2
      norm_num
      linarith
  · rw [hzim]
    rw [Set.mem_Icc]
    have habs : |(t - rho.im) / R| ≤ 1 := by
      rw [abs_div, abs_of_pos hR]
      exact (div_le_one hR).mpr himNorm
    exact abs_le.mp habs

theorem fordCotKernel_fordParameters_eq_scaled_profile
    {t R : ℝ} (hR : 0 < R) (rho : ℂ) :
    fordCotKernel ((5 / 2 : ℝ) * R)
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho) =
      (((1 / R : ℝ) : ℂ) *
        ((((Real.pi / 5 : ℝ) : ℂ) *
          Complex.cot ((((Real.pi / 5 : ℝ) : ℂ) *
            fordLocalNormalizedDisplacement t R rho))))) := by
  unfold fordCotKernel fordLocalNormalizedDisplacement
  have hcoeff :
      (((Real.pi / (2 * ((5 / 2 : ℝ) * R)) : ℝ) : ℂ)) =
        ((1 / R : ℝ) : ℂ) * (((Real.pi / 5 : ℝ) : ℂ)) := by
    push_cast
    field_simp [hR.ne']
  have harg :
      (((Real.pi / (2 * ((5 / 2 : ℝ) * R)) : ℝ) : ℂ) *
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho)) =
        (((Real.pi / 5 : ℝ) : ℂ) *
          ((fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t - rho) / (R : ℂ))) := by
    push_cast
    field_simp [hR.ne']
  rw [harg, hcoeff]
  ring

theorem fordCotKernel_fordParameters_re_lower
    {t R : ℝ} (hR : 0 < R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    fordLocalCotLowerConstant / R ≤
      (fordCotKernel ((5 / 2 : ℝ) * R)
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho)).re := by
  let z := fordLocalNormalizedDisplacement t R rho
  have hz : z ∈ fordLocalCotRegion :=
    fordLocalNormalizedDisplacement_mem_region hR hrho
  have hmin := fordLocalCotLowerConstant_le hz
  have heq := fordCotKernel_fordParameters_eq_scaled_profile
    (t := t) hR rho
  rw [heq]
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [← fordLocalCotProfile_eq_complex]
  change fordLocalCotLowerConstant / R ≤ (1 / R) * fordLocalCotProfile z
  simpa [div_eq_mul_inv, mul_comm] using
    ((div_le_div_iff_of_pos_right hR).mpr hmin)

theorem fordLocalDisk_zeroContribution_le
    {t R : ℝ} (hR : 0 < R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    ((analyticVanishingOrder riemannZeta rho : ℂ) *
      fordCotKernel ((5 / 2 : ℝ) * R)
        (rho - fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t)).re ≤
      -((analyticVanishingOrder riemannZeta rho : ℝ) *
        (fordLocalCotLowerConstant / R)) := by
  have hlower := fordCotKernel_fordParameters_re_lower hR hrho
  have hneg :
      fordCotKernel ((5 / 2 : ℝ) * R)
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t) =
        -fordCotKernel ((5 / 2 : ℝ) * R)
          (fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t - rho) := by
    rw [show rho - fordShiftedDetectorCenter
      (1 + (6421 / 10000 : ℝ) * R) t =
        -(fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho) by ring,
      fordCotKernel_neg]
  rw [hneg, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero, neg_re]
  have hm : 0 ≤ (analyticVanishingOrder riemannZeta rho : ℝ) := by positivity
  nlinarith

theorem sum_fordLocalDisk_zeroContribution_le
    {t R : ℝ} (hR : 0 < R) :
    (∑ rho ∈ fordLocalDiskZeros t R,
      ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel ((5 / 2 : ℝ) * R)
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t)).re) ≤
      -((fordLocalDiskZeroCount t R : ℝ) *
        (fordLocalCotLowerConstant / R)) := by
  calc
    (∑ rho ∈ fordLocalDiskZeros t R,
      ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel ((5 / 2 : ℝ) * R)
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t)).re)
        ≤ ∑ rho ∈ fordLocalDiskZeros t R,
          -((analyticVanishingOrder riemannZeta rho : ℝ) *
            (fordLocalCotLowerConstant / R)) := by
          gcongr with rho hrho
          exact fordLocalDisk_zeroContribution_le hR hrho
    _ = -((fordLocalDiskZeroCount t R : ℝ) *
        (fordLocalCotLowerConstant / R)) := by
      rw [fordLocalDiskZeroCount]
      push_cast
      rw [Finset.sum_neg_distrib, Finset.sum_mul]

end

end GafniTao
