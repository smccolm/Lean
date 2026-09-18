import Tao2026.SmoothNumberSaddleFiniteHeightPerron

/-!
# Assembly of the finite-height saddle inversion

At the quarter-epsilon HT ceiling, the normalized Perron line splits exactly
into the central Gaussian contribution, the principal-phase annulus, and the
HT outer shell.  Their three limits, together with finite-height sharp Perron
inversion, close the critical smooth-number saddle asymptotic.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Interval

namespace Tao2026

noncomputable section

/-- Exact finite-height decomposition at the quarter-epsilon HT ceiling. -/
theorem smoothSaddleNormalizedPerronLine_quarter_eq_central_add_wide_add_outer
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleNormalizedPerronLine X y
        (smoothSaddleHTFrequencyCeiling y (1 / 4)) =
      smoothSaddleCentralLaplaceContribution X y +
        smoothSaddleWideAnnularPerronContribution X y +
        smoothSaddleHTOuterPerronContributionQuarter X y := by
  let Hc := smoothSaddleCentralPerronHeight X y
  let Hw := smoothSaddleWidePerronHeight X y
  let T := smoothSaddleHTFrequencyCeiling y (1 / 4)
  have hcomp := smoothSaddleComplementaryPerronLine_eq_tailIntegrals
    hX hy T
  have hadd := smoothSaddleSymmetricPerronShellContribution_add_adjacent
    hX hy Hc Hw T
  have htail : smoothSaddleComplementaryPerronLine X y T =
      smoothSaddleSymmetricPerronShellContribution X y Hc T := by
    simpa only [smoothSaddleSymmetricPerronShellContribution, Hc] using hcomp
  have hwide : smoothSaddleSymmetricPerronShellContribution X y Hc Hw =
      smoothSaddleWideAnnularPerronContribution X y := by
    rfl
  have houter : smoothSaddleSymmetricPerronShellContribution X y Hw T =
      smoothSaddleHTOuterPerronContributionQuarter X y := by
    rfl
  calc
    smoothSaddleNormalizedPerronLine X y T =
        smoothSaddleComplementaryPerronLine X y T +
          smoothSaddleCentralLaplaceContribution X y := by
      unfold smoothSaddleComplementaryPerronLine
      ring
    _ = smoothSaddleSymmetricPerronShellContribution X y Hc T +
          smoothSaddleCentralLaplaceContribution X y := by rw [htail]
    _ = (smoothSaddleSymmetricPerronShellContribution X y Hc Hw +
          smoothSaddleSymmetricPerronShellContribution X y Hw T) +
          smoothSaddleCentralLaplaceContribution X y := by rw [hadd]
    _ = smoothSaddleCentralLaplaceContribution X y +
        smoothSaddleWideAnnularPerronContribution X y +
        smoothSaddleHTOuterPerronContributionQuarter X y := by
      rw [hwide, houter]
      ring

/-- The complete normalized finite Perron line tends to one at the enlarged
HT ceiling. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleNormalizedPerronLine_quarter_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleNormalizedPerronLine (X n) (y n)
      (smoothSaddleHTFrequencyCeiling (y n) (1 / 4))) atTop (𝓝 1) := by
  have hsum :=
    (hregime.tendsto_smoothSaddleCentralLaplaceContribution_one hα).add
      (hregime.tendsto_smoothSaddleWideAnnularPerronContribution_zero hα) |>.add
        (hregime.tendsto_smoothSaddleHTOuterPerronContributionQuarter_zero hα)
  have hsum' : Tendsto (fun n =>
      smoothSaddleCentralLaplaceContribution (X n) (y n) +
        smoothSaddleWideAnnularPerronContribution (X n) (y n) +
        smoothSaddleHTOuterPerronContributionQuarter (X n) (y n))
      atTop (𝓝 1) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  exact (smoothSaddleNormalizedPerronLine_quarter_eq_central_add_wide_add_outer
    hX hy).symm

/-- The finite-height contour assembly proves the critical smooth-number
saddle asymptotic in complex form. -/
theorem IsTaoCriticalSmoothRegime.tendsto_psiNat_div_smoothSaddleMainTerm_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => (psiNat (X n) (y n) : ℂ) /
      (smoothSaddleMainTerm (X n) (y n) : ℂ)) atTop (𝓝 1) := by
  have hline :=
    hregime.tendsto_smoothSaddleNormalizedPerronLine_quarter_one hα
  have herror :=
    hregime.tendsto_smoothSharpPerronQuarter_sub_psiNat_div_mainTerm_zero hα
  have hdiff := hline.sub herror
  have hdiff' : Tendsto (fun n =>
      smoothSaddleNormalizedPerronLine (X n) (y n)
          (smoothSaddleHTFrequencyCeiling (y n) (1 / 4)) -
        (((∑' m : Nat.smoothNumbers (y n + 1),
            GafniTao.sharpPerronKernel
              (smoothSaddlePoint (X n) (y n))
              (smoothSaddleHTFrequencyCeiling (y n) (1 / 4))
              (X n) m.1) - (psiNat (X n) (y n) : ℂ)) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ))) atTop (𝓝 1) := by
    simpa using hdiff
  apply hdiff'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  rw [smoothSaddleNormalizedPerronLine_eq_tsum_div_mainTerm hX hy]
  ring

/-- The critical smooth-number saddle asymptotic, with no remaining local
limit or Perron-tail hypothesis. -/
theorem taoCriticalSmoothSaddleAsymptoticConclusion :
    TaoCriticalSmoothSaddleAsymptoticConclusion := by
  intro α X y hα hregime
  have hcomplex := hregime.tendsto_psiNat_div_smoothSaddleMainTerm_one hα
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  apply hreal.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  change ((psiNat (X n) (y n) : ℂ) /
      (smoothSaddleMainTerm (X n) (y n) : ℂ)).re =
    (psiNat (X n) (y n) : ℝ) /
      smoothSaddleMainTerm (X n) (y n)
  rw [Complex.div_re]
  norm_num
  field_simp [(smoothSaddleMainTerm_pos hX hy).ne']

end

end Tao2026
