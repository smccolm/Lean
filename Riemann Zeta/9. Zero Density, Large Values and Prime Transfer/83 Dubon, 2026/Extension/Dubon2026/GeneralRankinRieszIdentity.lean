import Dubon2026.GeneralRankinDualCutoffs
import Dubon2026.RankinPerronContourShift

/-! # The actual general-level Rankin Riesz sum and its finite family of genuine dual series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The finite signed sum of actual divisor Gamma series with their genuine component conductors. -/
def generalRankinGammaDualSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) : ℂ :=
  ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k * divisorGammaDualSeries f d x

/-- The actual general-level left Perron contour tends to the finite signed family of genuine Gamma dual series. -/
theorem tendsto_general_rankinPerronVerticalCutoff_dual {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    Tendsto (rankinPerronVerticalCutoff f x (-1 / 8)) atTop (𝓝 (generalRankinGammaDualSeries f x)) := by
  have ht := tendsto_finsetSum Finset.univ (fun d _ =>
    (tendsto_divisorGammaDualCutoffSeries f hk d hx).const_mul (divisorRankinAmplitude Q d.val k))
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun T => (general_rankinPerronVerticalCutoff_eq_dualCutoffs f hk hx T).symm)

/-- The genuine general-level quadratic Riesz sum equals both actual pole terms plus the exact finite signed divisor Gamma series. -/
theorem general_rankinConvolutionRiesz_eq_dual {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    (rankinConvolutionRiesz f x : ℂ) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 + generalRankinGammaDualSeries f x := by
  have he := tendsto_nhds_unique (tendsto_rankinPerronVerticalCutoff_left f hk hx)
    (tendsto_general_rankinPerronVerticalCutoff_dual f hk hx)
  linear_combination he

/-- The literal general-level Riesz error consists of its actual quadratic pole term and genuine finite dual series. -/
theorem general_rankinConvolutionRieszError_eq_dual {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    (rankinConvolutionRieszError f x : ℂ) =
      -rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 + generalRankinGammaDualSeries f x := by
  change ((rankinConvolutionRiesz f x - rankinConvolutionResidue f * x ^ 3 / 6 : ℝ) : ℂ) = _
  push_cast
  rw [general_rankinConvolutionRiesz_eq_dual f hk hx]
  ring

end
end Dubon2026
