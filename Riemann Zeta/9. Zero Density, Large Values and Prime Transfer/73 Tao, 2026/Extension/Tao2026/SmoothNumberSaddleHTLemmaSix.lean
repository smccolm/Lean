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

/-- The shape of the error majorant in HT Lemma 6, equation (3.10), before
the source's epsilon-dependent implied constant is inserted. -/
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

/-- HT Lemma 6 at a fixed `epsilon` and with a displayed admissible implied
coefficient.  The paper states (3.10) with `O_epsilon`, so replacing `C` by the
literal value one would be a strictly stronger, and generally false, claim. -/
def SmoothSaddleHTMangoldtTransformEstimateAt (ε C : ℝ) : Prop :=
  0 < C ∧ ∀ (y : ℕ) (β t : ℝ),
    2 ≤ y → 0 < β → β < 1 →
      |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
        ‖smoothSaddleHTMangoldtTransform y β t -
            smoothSaddleHTMangoldtMainTerm y β t‖ ≤
          C * smoothSaddleHTMangoldtError y β ε

/-- The source-faithful uniform analytic assertion of HT Lemma 6.  This
coefficient is uniform in `y`, `beta`, and `t`, and may depend on `epsilon`,
exactly as indicated by the paper's `O_epsilon` notation. -/
def SmoothSaddleHTMangoldtTransformEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℝ, SmoothSaddleHTMangoldtTransformEstimateAt ε C

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

/-- A fixed-constant Lemma 6 estimate supplies both frequencies required by
its weighted-cosine corollary. -/
theorem SmoothSaddleHTMangoldtTransformEstimateAt.cosine
    {ε C : ℝ} (hHT : SmoothSaddleHTMangoldtTransformEstimateAt ε C)
    {y : ℕ} {β t : ℝ}
    (hy : 2 ≤ y) (hβ : 0 < β) (hβOne : β < 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    |smoothSaddleHTMangoldtCosineSum y β t -
      smoothSaddleHTMangoldtCosineMainTerm y β t| ≤
        2 * C * smoothSaddleHTMangoldtError y β ε := by
  have hbound := hHT.2
  have hresult := abs_smoothSaddleHTMangoldtCosineSum_sub_mainTerm_le
    (y := y) (β := β) (t := t)
    (E := C * smoothSaddleHTMangoldtError y β ε)
    (hbound y β 0 hy hβ hβOne
      (by simpa using (smoothSaddleHTFrequencyCeiling_pos y ε).le)
    ) (hbound y β t hy hβ hβOne ht)
  simpa [mul_assoc] using hresult

/-- The global `O_epsilon` contract yields one positive constant which works
uniformly in the complete cosine estimate at the selected `epsilon`. -/
theorem SmoothSaddleHTMangoldtTransformEstimate.exists_cosine_constant
    (hHT : SmoothSaddleHTMangoldtTransformEstimate)
    {ε : ℝ} (hε : 0 < ε) (hεOne : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℕ) (β t : ℝ),
      2 ≤ y → 0 < β → β < 1 →
        |t| ≤ smoothSaddleHTFrequencyCeiling y ε →
          |smoothSaddleHTMangoldtCosineSum y β t -
            smoothSaddleHTMangoldtCosineMainTerm y β t| ≤
              2 * C * smoothSaddleHTMangoldtError y β ε := by
  obtain ⟨C, hC⟩ := hHT ε hε hεOne
  exact ⟨C, hC.1, fun y β t hy hβ hβOne ht =>
    hC.cosine hy hβ hβOne ht⟩

end

end Tao2026
