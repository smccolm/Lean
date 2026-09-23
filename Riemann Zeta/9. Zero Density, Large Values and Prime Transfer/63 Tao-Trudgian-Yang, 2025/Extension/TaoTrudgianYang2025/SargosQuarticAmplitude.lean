import TaoTrudgianYang2025.SargosQuarticClosedRange

/-! The actual inverse-curvature amplitude on the closed quartic stationary range. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

def sargosQuarticStationaryAmplitude (N α γ y : ℝ) : ℝ :=
  1/Real.sqrt (2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2)

theorem sargosQuarticSlope_inverse_closed {N α γ y : ℝ}
    (hN : 0 < N)
    (hy : y ∈ Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    sargosQuarticSlope α γ (sargosQuarticInverseSlope N α γ y) = y := by
  apply Function.invFunOn_eq
  exact intermediate_value_Icc (show N ≤ 2*N by linarith)
    (contDiff_sargosQuarticSlope α γ).continuous.continuousOn hy

theorem sargosQuarticInverseSlope_strictMonoOn_closed {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    StrictMonoOn (sargosQuarticInverseSlope N α γ)
      (Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) := by
  intro y hy z hz hyz
  have hw := sargosQuarticInverseSlope_mem_closed hN hα hγ hy
  have hv := sargosQuarticInverseSlope_mem_closed hN hα hγ hz
  by_contra h
  have hh := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn hv hw (le_of_not_gt h)
  rw [sargosQuarticSlope_inverse_closed hN hz,sargosQuarticSlope_inverse_closed hN hy] at hh
  exact (not_le_of_gt hyz) hh

theorem sargosQuarticStationaryAmplitude_pos_bound {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    0 < sargosQuarticStationaryAmplitude N α γ y ∧
      sargosQuarticStationaryAmplitude N α γ y ≤ 1/Real.sqrt α := by
  have hw := sargosQuarticInverseSlope_mem_closed hN hα hγ hy
  have hc := (sargosQuarticPhase_curvature hN hα hγ hw).1
  have hp : 0 < 2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 := by linarith
  refine ⟨by unfold sargosQuarticStationaryAmplitude; positivity,?_⟩
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hα) (Real.sqrt_le_sqrt (by linarith))

theorem sargosQuarticStationaryAmplitude_antitoneOn_of_nonneg {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) (hγ₀ : 0 ≤ γ) :
    AntitoneOn (sargosQuarticStationaryAmplitude N α γ)
      (Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) := by
  intro y hy z hz hyz
  have hw := sargosQuarticInverseSlope_mem_closed hN hα hγ hy
  have hm := (sargosQuarticInverseSlope_strictMonoOn_closed hN hα hγ).monotoneOn hy hz hyz
  have hs := pow_le_pow_left₀ (hN.le.trans hw.1) hm 2
  have hc : 2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 ≤
      2*α+12*γ*(sargosQuarticInverseSlope N α γ z)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hs (show 0 ≤ 12*γ by positivity)]
  have hp := sargosQuartic_curvature_pos hN hα hγ hw
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt hc)

theorem sargosQuarticStationaryAmplitude_monotoneOn_of_nonpos {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) (hγ₀ : γ ≤ 0) :
    MonotoneOn (sargosQuarticStationaryAmplitude N α γ)
      (Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) := by
  intro y hy z hz hyz
  have hw := sargosQuarticInverseSlope_mem_closed hN hα hγ hy
  have hv := sargosQuarticInverseSlope_mem_closed hN hα hγ hz
  have hm := (sargosQuarticInverseSlope_strictMonoOn_closed hN hα hγ).monotoneOn hy hz hyz
  have hs := pow_le_pow_left₀ (hN.le.trans hw.1) hm 2
  have hc : 2*α+12*γ*(sargosQuarticInverseSlope N α γ z)^2 ≤
      2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 := by
    nlinarith only [mul_le_mul_of_nonpos_left hs (show 12*γ ≤ 0 by linarith)]
  have hp := sargosQuartic_curvature_pos hN hα hγ hv
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt hc)

theorem sargosQuarticStationaryAmplitude_monotone_or_antitone {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    MonotoneOn (sargosQuarticStationaryAmplitude N α γ)
      (Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) ∨
    AntitoneOn (sargosQuarticStationaryAmplitude N α γ)
      (Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) := by
  rcases le_total γ 0 with h | h
  · exact Or.inl (sargosQuarticStationaryAmplitude_monotoneOn_of_nonpos hN hα hγ h)
  · exact Or.inr (sargosQuarticStationaryAmplitude_antitoneOn_of_nonneg hN hα hγ h)

theorem sargosQuarticStationaryMainTerm_norm_eq_amplitude (N α γ y : ℝ) :
    ‖sargosQuarticStationaryMainTerm N α γ y‖ = sargosQuarticStationaryAmplitude N α γ y := by
  simp only [sargosQuarticStationaryMainTerm,sargosQuarticStationaryAmplitude,norm_div,
    Circle.norm_coe,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

end TaoTrudgianYang2025

