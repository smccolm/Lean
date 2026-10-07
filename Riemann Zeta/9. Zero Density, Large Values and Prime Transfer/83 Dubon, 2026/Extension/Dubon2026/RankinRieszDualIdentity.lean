import Dubon2026.RankinPerronDualInterchange
import Dubon2026.RankinPerronContourShift
import Dubon2026.RankinGammaDualSeries

/-! # The actual full-level Rankin Riesz sum equals its genuine dual Gamma series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The actual full-level left Perron contour converges to the genuine Rankin dual series, by a uniform summable coefficient majorant. -/
theorem tendsto_rankinPerronVerticalCutoff_dual {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    Tendsto (rankinPerronVerticalCutoff f x (-1 / 8)) atTop
      (𝓝 (((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) x)) := by
  obtain ⟨B, hB, hb⟩ := exists_rankinConvolution_sum_upper f (by omega)
  have hc0 : (rankinConvolutionCoefficients f 0).re = 0 := by simp [rankinConvolutionCoefficients_zero]
  have hb' (N : ℕ) : (∑ n ∈ Finset.Icc 0 N, (rankinConvolutionCoefficients f n).re) ≤ B * N := by
    rw [sum_Icc_zero_eq_positive hc0]
    exact hb N
  have ht := tendsto_gammaRieszDualCutoffSeries (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    (show 0 < (4 * Real.pi ^ 2) ^ 2 by positivity)
    (rankinConvolutionCoefficients_re_nonneg f) hB.le hb' hx
  have ht' := ht.const_mul (((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹)
  apply ht'.congr'
  exact Filter.Eventually.of_forall (fun T => (rankinPerronVerticalCutoff_eq_dualCutoffs f hk hx T).symm)

/-- The actual quadratic Rankin Riesz sum has its exact cubic residue, quadratic zero-pole term and convergent coefficient-weighted dual Gamma series. -/
theorem rankinConvolutionRiesz_eq_dual {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    (rankinConvolutionRiesz f x : ℂ) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 +
        ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) x := by
  have he := tendsto_nhds_unique (tendsto_rankinPerronVerticalCutoff_left f hk hx)
    (tendsto_rankinPerronVerticalCutoff_dual f hk hx)
  linear_combination he

/-- The literal full-level Riesz error is the quadratic contribution plus the actual dual series. -/
theorem rankinConvolutionRieszError_eq_dual {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    (rankinConvolutionRieszError f x : ℂ) =
      -rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 +
        ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * rankinGammaDualSeries f ((4 * Real.pi ^ 2) ^ 2) x := by
  change ((rankinConvolutionRiesz f x - rankinConvolutionResidue f * x ^ 3 / 6 : ℝ) : ℂ) = _
  push_cast
  rw [rankinConvolutionRiesz_eq_dual f hk hx]
  push_cast
  ring

end
end Dubon2026
