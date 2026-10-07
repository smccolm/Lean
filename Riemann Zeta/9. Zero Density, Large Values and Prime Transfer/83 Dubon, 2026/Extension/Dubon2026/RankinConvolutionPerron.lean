import Dubon2026.RieszPerronIntegral
import Dubon2026.RankinConvolutionRiesz

/-! # The literal Perron integral for the actual Rankin convolution Riesz mean -/

namespace Dubon2026

open Complex MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual Rankin convolution Riesz mean is the inverse Mellin transform of its genuine Dirichlet series. -/
theorem rankinConvolutionRiesz_eq_mellinInv {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    (rankinConvolutionRiesz f x : ℂ) = (x : ℂ) ^ 2 * mellinInv σ
      (fun s => LSeries (rankinConvolutionCoefficients f) s * rieszMellinSymbol s) x⁻¹ := by
  have ha : LSeriesSummable (fun n => ((rankinConvolutionCoefficients f n).re : ℂ)) σ := by
    simpa only [rankinConvolutionCoefficients_ofReal_re] using
      rankinConvolution_lseriesSummable f hk (s := (σ : ℂ)) hσ
  simpa only [rankinConvolutionRiesz, rankinConvolutionCoefficients_ofReal_re] using
    rieszSecondSum_eq_perron (by linarith : 0 < σ) hx ha

/-- The exact Rankin Perron integral is absolutely convergent, with no summability hypothesis left to the caller. -/
theorem integrable_rankinConvolutionPerron {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + t * I + 2) *
      LSeries (rankinConvolutionCoefficients f) (σ + t * I) /
        (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2))) :=
  integrable_rieszPerron (by linarith) hx (rankinConvolution_lseriesSummable f hk hσ)

/-- The literal quadratic Rankin Riesz sum has the exact conventional vertical integral representation. -/
theorem rankinConvolutionRiesz_eq_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {σ x : ℝ} (hσ : 1 < σ) (hx : 0 < x) :
    (rankinConvolutionRiesz f x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + t * I + 2) *
          LSeries (rankinConvolutionCoefficients f) (σ + t * I) /
            (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2)) := by
  rw [← rieszPerron_integral_formula (by linarith : 0 < σ) hx
    (rankinConvolution_lseriesSummable f hk hσ), rankinConvolutionRiesz_eq]
  push_cast
  simp only [rankinConvolutionCoefficients_ofReal_re]

end
end Dubon2026
