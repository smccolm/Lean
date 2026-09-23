import TaoTrudgianYang2025.SargosQuarticBufferedStationary

/-! Uniform actual-coordinate distances and slope gaps on the extended quartic interval. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticMorseCoordinate_abs_bounds {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    |u-r|/2 ≤ |sargosQuarticMorseCoordinate ε r u| ∧
      |sargosQuarticMorseCoordinate ε r u| ≤ 2*|u-r| := by
  have h := sargosQuarticMorseCoordinate_sqrt_bounds hε hr hu
  rw [sargosQuarticMorseCoordinate,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 (abs_nonneg (u-r))]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 (abs_nonneg (u-r))]

theorem sargosQuarticMorseCoordinate_mul_deriv {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    sargosQuarticMorseCoordinate ε r u*deriv (sargosQuarticMorseCoordinate ε r) u =
      sargosQuarticSlope 1 ε u-sargosQuarticSlope 1 ε r := by
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr hu).1
  have hp' : 0 < sargosQuarticMorseCoefficient ε r u := by linarith
  have hs : Real.sqrt (2*sargosQuarticMorseCoefficient ε r u) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [(sargosQuarticMorseCoordinate_hasDerivAt hp').deriv,sargosQuarticMorseCoordinate]
  field_simp
  unfold sargosQuarticMorseNumerator sargosQuarticSlope
  ring

theorem sargosQuarticMorseInverse_window_slope_gaps {ε r H : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hH : 0 ≤ H)
    (hleft : -H ∈ sargosQuarticMorseRange ε r) (hright : H ∈ sargosQuarticMorseRange ε r) :
    7*H/16 ≤ sargosQuarticSlope 1 ε r-
        sargosQuarticSlope 1 ε (sargosQuarticMorseInverse ε r (-H)) ∧
      7*H/16 ≤ sargosQuarticSlope 1 ε (sargosQuarticMorseInverse ε r H)-
        sargosQuarticSlope 1 ε r := by
  have hu := sargosQuarticMorseInverse_mem hε hr hleft
  have hv := sargosQuarticMorseInverse_mem hε hr hright
  have hl := (sargosQuarticMorseCoordinate_deriv_bounds hε hr ⟨hu.1.le,hu.2.le⟩).1
  have hr' := (sargosQuarticMorseCoordinate_deriv_bounds hε hr ⟨hv.1.le,hv.2.le⟩).1
  have el := sargosQuarticMorseCoordinate_mul_deriv hε hr ⟨hu.1.le,hu.2.le⟩
  have er := sargosQuarticMorseCoordinate_mul_deriv hε hr ⟨hv.1.le,hv.2.le⟩
  rw [sargosQuarticMorseCoordinate_inverse hleft] at el
  rw [sargosQuarticMorseCoordinate_inverse hright] at er
  have h₁ := mul_le_mul_of_nonneg_left hl hH
  have h₂ := mul_le_mul_of_nonneg_left hr' hH
  constructor <;> nlinarith

end TaoTrudgianYang2025

