import Dubon2026.RankinPerronPoles
import Dubon2026.RankinPerronHorizontal

/-! # Exact finite Rankin Perron contour transfer and its genuine original vertical limit -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The actual normalized symmetric vertical cutoff of the continued Rankin Perron function. -/
def rankinPerronVerticalCutoff {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x β T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, rankinPerronContinuation f x (gammaVerticalPoint β t)

/-- The literal actual right vertical integrand is absolutely integrable by the already proved Rankin Perron theorem. -/
theorem integrable_rankinPerronContinuation_right {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {x β : ℝ} (hx : 0 < x) (hβ : 1 < β) :
    Integrable (fun t : ℝ => rankinPerronContinuation f x (gammaVerticalPoint β t)) := by
  have he : (fun t : ℝ => rankinPerronContinuation f x (gammaVerticalPoint β t)) =
      (fun t : ℝ => (x : ℂ) ^ ((β : ℂ) + t * I + 2) *
        LSeries (rankinConvolutionCoefficients f) (β + t * I) /
          (((β : ℂ) + t * I) * ((β : ℂ) + t * I + 1) * ((β : ℂ) + t * I + 2))) := by
    funext t
    exact rankinPerronContinuation_eq_series f hk x (by simpa only [gammaVerticalPoint_re] using hβ)
  rw [he]
  exact integrable_rankinConvolutionPerron f hk hβ hx

/-- The actual right vertical cutoff converges to the literal quadratic Rankin sum. -/
theorem tendsto_rankinPerronVerticalCutoff_right {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {x β : ℝ} (hx : 0 < x) (hβ : 1 < β) :
    Tendsto (rankinPerronVerticalCutoff f x β) atTop (𝓝 (rankinConvolutionRiesz f x : ℂ)) := by
  have hi := integrable_rankinPerronContinuation_right f hk hx hβ
  have ht := (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id).const_smul
    (1 / (2 * Real.pi) : ℝ)
  change Tendsto (rankinPerronVerticalCutoff f x β) atTop
    (𝓝 ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, rankinPerronContinuation f x (gammaVerticalPoint β t))) at ht
  have he : ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, rankinPerronContinuation f x (gammaVerticalPoint β t)) =
      (rankinConvolutionRiesz f x : ℂ) := by
    rw [rankinConvolutionRiesz_eq_integral f hk hβ hx]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact rankinPerronContinuation_eq_series f hk x (by simpa only [gammaVerticalPoint_re] using hβ)
  rwa [he] at ht

end
end Dubon2026
