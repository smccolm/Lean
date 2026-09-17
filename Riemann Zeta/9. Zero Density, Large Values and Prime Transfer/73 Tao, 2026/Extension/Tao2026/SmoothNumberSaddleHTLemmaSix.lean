import Tao2026.SmoothNumberSaddleHTMangoldtTransform

/-!
# The exact Hildebrand--Tenenbaum Lemma 6 contract

This module records the source's full frequency ceiling
`Y_ε(y) = exp ((log y)^(3/2-ε))`, its transform-error scale, and the precise
uniform proposition still required from shifted Perron inversion and the
Vinogradov zero-free region.  It also computes the complex main term exactly
and derives the weighted-cosine corollary with the source error factor two.

The proposition is intentionally named rather than postulated as an axiom.
Its analytic proof remains the next contour-theoretic task.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The frequency ceiling `Y(ε)` fixed immediately before HT Lemma 1 and used
in Lemma 6. -/
noncomputable def smoothSaddleHTFrequencyCeiling (y : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ((Real.log y) ^ ((3 : ℝ) / 2 - ε))

/-- The error majorant in HT Lemma 6, equation (3.10). -/
noncomputable def smoothSaddleHTMangoldtError
    (y : ℕ) (β ε : ℝ) : ℝ :=
  (1 / β) *
    (1 + (y : ℝ) ^ β *
      Real.exp (-(Real.log y) ^ (ε / 2)))

theorem smoothSaddleHTFrequencyCeiling_pos (y : ℕ) (ε : ℝ) :
    0 < smoothSaddleHTFrequencyCeiling y ε := by
  unfold smoothSaddleHTFrequencyCeiling
  positivity

theorem smoothSaddleHTMangoldtError_nonneg
    (y : ℕ) {β ε : ℝ} (hβ : 0 < β) :
    0 ≤ smoothSaddleHTMangoldtError y β ε := by
  unfold smoothSaddleHTMangoldtError
  positivity

/-- The exact uniform analytic assertion of HT Lemma 6.  Proving this named
proposition requires shifted Perron inversion; the unshifted quantitative-PNT
estimate alone loses a factor proportional to `|t|` under Abel summation and
does not reach this frequency ceiling. -/
def SmoothSaddleHTMangoldtTransformEstimate : Prop :=
  ∀ (y : ℕ) (β ε t : ℝ),
    2 ≤ y → 0 < β → β < 1 → 0 < ε → ε < 1 →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
        ‖smoothSaddleHTMangoldtTransform y β t -
            smoothSaddleHTMangoldtMainTerm y β t‖ ≤
          smoothSaddleHTMangoldtError y β ε

/-- At frequency zero the complex source main term is simply `y^β / β`.
This remains true at `β = 0` under Lean's totalized division convention. -/
theorem smoothSaddleHTMangoldtMainTerm_zero (y : ℕ) (β : ℝ) :
    smoothSaddleHTMangoldtMainTerm y β 0 =
      ((((y : ℝ) ^ β / β : ℝ)) : ℂ) := by
  unfold smoothSaddleHTMangoldtMainTerm
  simp

/-- Cartesian closed form of the real part of the HT main term. -/
theorem smoothSaddleHTMangoldtMainTerm_re
    {y : ℕ} {β t : ℝ} (hden : β ^ 2 + t ^ 2 ≠ 0) :
    (smoothSaddleHTMangoldtMainTerm y β t).re =
      (y : ℝ) ^ β *
        (β * Real.cos (t * Real.log y) +
          t * Real.sin (t * Real.log y)) / (β ^ 2 + t ^ 2) := by
  have hexp_re (r : ℝ) :
      (Complex.exp (-(r : ℂ) * Complex.I)).re = Real.cos r := by
    simp [Complex.exp_re]
  have hexp_im (r : ℝ) :
      (Complex.exp (-(r : ℂ) * Complex.I)).im = -Real.sin r := by
    simp [Complex.exp_im]
  unfold smoothSaddleHTMangoldtMainTerm
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im]
  rw [hexp_re, hexp_im]
  simp [Complex.normSq_apply]
  field_simp [hden]

/-- Exact norm of the source main term. -/
theorem norm_smoothSaddleHTMangoldtMainTerm (y : ℕ) (β t : ℝ) :
    ‖smoothSaddleHTMangoldtMainTerm y β t‖ =
      |(y : ℝ) ^ β| / Real.sqrt (β ^ 2 + t ^ 2) := by
  have hexp_norm (r : ℝ) :
      ‖Complex.exp (-(r : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  unfold smoothSaddleHTMangoldtMainTerm
  rw [norm_div, norm_mul]
  rw [hexp_norm]
  simp [Complex.norm_def, Complex.normSq_apply]
  congr 2
  ring

/-- Cartesian form of the real main term in the cosine corollary to Lemma 6. -/
theorem smoothSaddleHTMangoldtCosineMainTerm_eq
    {y : ℕ} {β t : ℝ} (hden : β ^ 2 + t ^ 2 ≠ 0) :
    smoothSaddleHTMangoldtCosineMainTerm y β t =
      (y : ℝ) ^ β / β -
        (y : ℝ) ^ β *
          (β * Real.cos (t * Real.log y) +
            t * Real.sin (t * Real.log y)) / (β ^ 2 + t ^ 2) := by
  unfold smoothSaddleHTMangoldtCosineMainTerm
  rw [Complex.sub_re, smoothSaddleHTMangoldtMainTerm_zero]
  simp only [Complex.ofReal_re]
  rw [smoothSaddleHTMangoldtMainTerm_re hden]

/-- The named Lemma 6 estimate supplies both frequencies required by its
weighted-cosine corollary. -/
theorem SmoothSaddleHTMangoldtTransformEstimate.cosine
    (hHT : SmoothSaddleHTMangoldtTransformEstimate)
    {y : ℕ} {β ε t : ℝ}
    (hy : 2 ≤ y) (hβ : 0 < β) (hβOne : β < 1)
    (hε : 0 < ε) (hεOne : ε < 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    |smoothSaddleHTMangoldtCosineSum y β t -
      smoothSaddleHTMangoldtCosineMainTerm y β t| ≤
        2 * smoothSaddleHTMangoldtError y β ε := by
  apply abs_smoothSaddleHTMangoldtCosineSum_sub_mainTerm_le
  · exact hHT y β ε 0 hy hβ hβOne hε hεOne
      (by simpa using (smoothSaddleHTFrequencyCeiling_pos y ε).le)
  · exact hHT y β ε t hy hβ hβOne hε hεOne ht

end

end Tao2026
