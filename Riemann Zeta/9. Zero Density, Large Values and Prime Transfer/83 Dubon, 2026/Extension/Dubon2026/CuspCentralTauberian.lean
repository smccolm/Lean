import Dubon2026.NewmanSquareLaplace
import Dubon2026.NewmanTauberian
import Dubon2026.CuspRankinMean

/-! # Analytic Tauberian convergence for the actual centered cusp square mean -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The actual removed-pole Rankin function supplies a holomorphic continuation of the centered logarithmic mean's Laplace transform. -/
def cuspSquareErrorLaplace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (z : ℂ) : ℂ :=
  (cuspRankinRegular f (z + 1) - cuspRankinResidue f) / (z + 1)

/-- This genuine continuation is holomorphic on a fixed half-plane beyond the Tauberian boundary. -/
theorem differentiableOn_cuspSquareErrorLaplace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    DifferentiableOn ℂ (cuspSquareErrorLaplace f) {z : ℂ | -(1 / 4 : ℝ) ≤ z.re} := by
  have hh : DifferentiableOn ℂ (fun z : ℂ => cuspRankinRegular f (z + 1))
      {z : ℂ | -(1 / 4 : ℝ) ≤ z.re} :=
    (differentiableOn_cuspRankinRegular f hk).comp (by fun_prop) (by
      intro z hz
      change -(1 / 4 : ℝ) ≤ z.re at hz
      change 1 / 2 < (z + 1).re
      simp only [add_re, one_re]
      linarith)
  apply (hh.sub_const (cuspRankinResidue f : ℂ)).div (by fun_prop)
  intro z hz he
  have hre := congrArg Complex.re he
  change -(1 / 4 : ℝ) ≤ z.re at hz
  simp only [add_re, one_re, zero_re] at hre
  linarith

/-- In its convergence half-plane this continuation equals the literal centered cusp Laplace integral. -/
theorem cuspSquareErrorLaplace_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {z : ℂ} (hz : 0 < z.re) :
    cuspSquareErrorLaplace f z =
      newmanLaplace (newmanSquareError (normalizedCuspCoefficients f) (cuspRankinResidue f)) z := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_cusp_square_upper f hk
  rw [newmanSquareError_laplace hB.le hb (cuspRankinResidue f) hz, cuspSquareErrorLaplace,
    cuspRankinRegular_eq_series_sub_pole f hk (by simpa using hz)]
  have hz0 : z ≠ 0 := by intro h; subst z; simp at hz
  have hz1 : z + 1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  simp only [add_sub_cancel_right, cuspRankinSeries]
  field_simp [hz0, hz1]
  ring

/-- Newman inversion now applies to the actual normalized cusp coefficient square error, with every analytic input discharged. -/
theorem tendsto_cusp_square_error_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      newmanSquareError (normalizedCuspCoefficients f) (cuspRankinResidue f) t)
      atTop (𝓝 (cuspSquareErrorLaplace f 0)) := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_cusp_square_upper f hk
  apply newman_tauberian_integral
    (measurable_newmanSquareError _ _).aestronglyMeasurable
    (fun t _ => norm_newmanSquareError_le hB.le hb _ t) (by norm_num : (0 : ℝ) < 1 / 4)
    (differentiableOn_cuspSquareErrorLaplace f hk)
  exact fun z hz => cuspSquareErrorLaplace_eq f hk hz

/-- The continued value at zero has the exact actual Rankin regular-part normalization. -/
theorem cuspSquareErrorLaplace_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    cuspSquareErrorLaplace f 0 = cuspRankinRegular f 1 - cuspRankinResidue f := by
  simp [cuspSquareErrorLaplace]

end
end Dubon2026
