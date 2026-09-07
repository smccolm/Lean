import GafniTao.FordLocalCotangentUniform

/-!
# Uniform local-disk contribution for a selected good shift
-/

open Complex Finset Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLocal_selected_parameter_mem
    {t R eta' : ℝ} (hR : 0 < R)
    (hetaLower : (5 / 2 : ℝ) * R ≤ eta')
    (hetaUpper : eta' ≤ 3 * R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    (eta' / R, fordLocalNormalizedDisplacement t R rho) ∈
      fordLocalCotParameterRegion := by
  constructor
  · constructor
    · exact (le_div_iff₀ hR).mpr (by simpa [mul_comm] using hetaLower)
    · exact (div_le_iff₀ hR).mpr (by simpa [mul_comm] using hetaUpper)
  · exact fordLocalNormalizedDisplacement_mem_region hR hrho

theorem fordCotKernel_selected_eq_scaled_uniformProfile
    {t R eta' : ℝ} (hR : 0 < R) (rho : ℂ) :
    fordCotKernel eta'
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho) =
      (((1 / R : ℝ) : ℂ) *
        ((((Real.pi / (2 * (eta' / R)) : ℝ) : ℂ) *
          Complex.cot
            ((((Real.pi / (2 * (eta' / R)) : ℝ) : ℂ) *
              fordLocalNormalizedDisplacement t R rho))))) := by
  unfold fordCotKernel fordLocalNormalizedDisplacement
  have hcoeff :
      (((Real.pi / (2 * eta') : ℝ) : ℂ)) =
        ((1 / R : ℝ) : ℂ) *
          (((Real.pi / (2 * (eta' / R)) : ℝ) : ℂ)) := by
    push_cast
    by_cases heta : eta' = 0
    · simp [heta]
    · field_simp [hR.ne', heta]
  have harg :
      (((Real.pi / (2 * eta') : ℝ) : ℂ) *
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho)) =
        (((Real.pi / (2 * (eta' / R)) : ℝ) : ℂ) *
          ((fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t - rho) / (R : ℂ))) := by
    push_cast
    by_cases heta : eta' = 0
    · simp [heta]
    · field_simp [hR.ne', heta]
  rw [harg, hcoeff]
  ring

theorem fordCotKernel_selected_re_lower
    {t R eta' : ℝ} (hR : 0 < R)
    (hetaLower : (5 / 2 : ℝ) * R ≤ eta')
    (hetaUpper : eta' ≤ 3 * R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    fordLocalCotUniformLowerConstant / R ≤
      (fordCotKernel eta'
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t - rho)).re := by
  let q := eta' / R
  let z := fordLocalNormalizedDisplacement t R rho
  have hp : (q, z) ∈ fordLocalCotParameterRegion :=
    fordLocal_selected_parameter_mem hR hetaLower hetaUpper hrho
  have hmin := fordLocalCotUniformLowerConstant_le hp
  rw [fordCotKernel_selected_eq_scaled_uniformProfile hR rho]
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [← fordLocalCotUniformProfile_eq_complex]
  change fordLocalCotUniformLowerConstant / R ≤
    (1 / R) * fordLocalCotUniformProfile (q, z)
  simpa [div_eq_mul_inv, mul_comm] using
    ((div_le_div_iff_of_pos_right hR).mpr hmin)

theorem fordLocalDisk_selected_zeroContribution_le
    {t R eta' : ℝ} (hR : 0 < R)
    (hetaLower : (5 / 2 : ℝ) * R ≤ eta')
    (hetaUpper : eta' ≤ 3 * R) {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    ((analyticVanishingOrder riemannZeta rho : ℂ) *
      fordCotKernel eta'
        (rho - fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t)).re ≤
      -((analyticVanishingOrder riemannZeta rho : ℝ) *
        (fordLocalCotUniformLowerConstant / R)) := by
  have hlower := fordCotKernel_selected_re_lower
    hR hetaLower hetaUpper hrho
  have hneg :
      fordCotKernel eta'
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t) =
        -fordCotKernel eta'
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

theorem sum_fordLocalDisk_selected_zeroContribution_le
    {t R eta' : ℝ} (hR : 0 < R)
    (hetaLower : (5 / 2 : ℝ) * R ≤ eta')
    (hetaUpper : eta' ≤ 3 * R) :
    (∑ rho ∈ fordLocalDiskZeros t R,
      ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta'
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t)).re) ≤
      -((fordLocalDiskZeroCount t R : ℝ) *
        (fordLocalCotUniformLowerConstant / R)) := by
  calc
    (∑ rho ∈ fordLocalDiskZeros t R,
      ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta'
          (rho - fordShiftedDetectorCenter
            (1 + (6421 / 10000 : ℝ) * R) t)).re)
        ≤ ∑ rho ∈ fordLocalDiskZeros t R,
          -((analyticVanishingOrder riemannZeta rho : ℝ) *
            (fordLocalCotUniformLowerConstant / R)) := by
          gcongr with rho hrho
          exact fordLocalDisk_selected_zeroContribution_le
            hR hetaLower hetaUpper hrho
    _ = -((fordLocalDiskZeroCount t R : ℝ) *
        (fordLocalCotUniformLowerConstant / R)) := by
      rw [fordLocalDiskZeroCount]
      push_cast
      rw [Finset.sum_neg_distrib, Finset.sum_mul]

end

end GafniTao
