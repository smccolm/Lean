import Tao2026.SmoothNumberSaddleHTLogDerivativeSymmetry
import GafniTao.FordKFiniteRectangle

/-!
# Low-height logarithmic derivative near the zeta pole

The HT left edge crosses ordinate zero, outside the high-height Landau
coordinate.  On a fixed VK zero-free rectangle the entire surrogate
`(s-1) zeta(s)` has no zeros, so its logarithmic derivative is bounded by
compactness.  Restoring zeta contributes only the explicit pole term
`1/(s-1)`.
-/

open Complex Set Topology
open RiemannZeta.GuthMaynard

namespace Tao2026

noncomputable section

/-- Fixed compact rectangle to the right of half the VK boundary. -/
noncomputable def smoothSaddleHTLowHeightCompact (c H : ℝ) : Set ℂ :=
  Set.Icc (1 - c / (2 * GafniTao.vinogradovKorobovDenominator H)) 2 ×ℂ
    Set.Icc (-H) H

theorem isCompact_smoothSaddleHTLowHeightCompact (c H : ℝ) :
    IsCompact (smoothSaddleHTLowHeightCompact c H) := by
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem sharpZetaSurrogate_ne_zero_on_smoothSaddleHTLowHeightCompact
    {c H : ℝ} (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    {z : ℂ} (hz : z ∈ smoothSaddleHTLowHeightCompact c H) :
    GafniTao.sharpZetaSurrogate z ≠ 0 := by
  have hD : 0 < GafniTao.vinogradovKorobovDenominator H :=
    GafniTao.vinogradovKorobovDenominator_pos hH
  have hHpos : 0 < H := (Real.exp_pos (Real.exp 1)).trans_le hH
  have hwidthPos : 0 < c / GafniTao.vinogradovKorobovDenominator H :=
    div_pos hc hD
  have hwidthLe : c / GafniTao.vinogradovKorobovDenominator H ≤ 1 :=
    (hZeroFree (T := H) le_rfl).2.1
  have hzRe : z.re ∈ Set.Icc
      (1 - c / (2 * GafniTao.vinogradovKorobovDenominator H)) 2 := hz.1
  have hzIm : z.im ∈ Set.Icc (-H) H := hz.2
  have hhalf : c / (2 * GafniTao.vinogradovKorobovDenominator H) =
      (c / GafniTao.vinogradovKorobovDenominator H) / 2 := by ring
  rw [hhalf] at hzRe
  by_cases hzOne : z = 1
  · simp [hzOne]
  · intro hsur
    have hzeta : riemannZeta z = 0 :=
      (GafniTao.sharpZetaSurrogate_eq_zero_iff hzOne).mp hsur
    by_cases hzRight : z.re ≤ 1
    · have hzRect : z ∈ Rectangle
          ((-(1 / 2 : ℝ) : ℂ) - (H : ℂ) * Complex.I)
          ((2 : ℂ) + (H : ℂ) * Complex.I) := by
        constructor
        · simp only [Set.mem_preimage, sub_re, neg_re, ofReal_re, mul_re,
            ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_re,
            add_zero]
          norm_num
          constructor <;> linarith [hzRe.1]
        · simp only [Set.mem_preimage, sub_im, neg_im, ofReal_im, mul_im,
            ofReal_re, I_im, I_re, zero_mul, mul_one, add_zero, add_im,
            neg_zero, zero_sub]
          norm_num
          rw [Set.uIcc_of_le (by linarith : -H ≤ H)]
          constructor <;> linarith [hzIm.1, hzIm.2]
      have hzSet : z ∈ GafniTao.zeroSet 0 H :=
        GafniTao.mem_zeroSet_of_zeta_zero_of_fordKRectangle
          (alpha := 2) (by norm_num) (by linarith) hzRect hzeta
      have hzLeft := (hZeroFree (T := H) le_rfl).2.2 hzSet
      linarith [hzRe.1]
    · exact (riemannZeta_ne_zero_of_one_lt_re (lt_of_not_ge hzRight)) hzeta

/-- The entire-surrogate logarithmic derivative is uniformly bounded on the
fixed low-height VK rectangle. -/
theorem exists_norm_logDeriv_sharpZetaSurrogate_lowHeight_le
    {c H : ℝ} (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ smoothSaddleHTLowHeightCompact c H,
      ‖logDeriv GafniTao.sharpZetaSurrogate z‖ ≤ C := by
  have hcont : ContinuousOn
      (fun z : ℂ => ‖logDeriv GafniTao.sharpZetaSurrogate z‖)
      (smoothSaddleHTLowHeightCompact c H) := by
    intro z hz
    exact (GafniTao.differentiableAt_logDeriv_sharpZetaSurrogate
      (sharpZetaSurrogate_ne_zero_on_smoothSaddleHTLowHeightCompact
        hc hH hZeroFree hz)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ :=
    (isCompact_smoothSaddleHTLowHeightCompact c H).bddAbove_image hcont
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  exact (hB (Set.mem_image_of_mem _ hz)).trans (le_max_right _ _)

/-- On the fixed low-height rectangle, zeta's logarithmic derivative is the
bounded surrogate term plus its explicit simple-pole contribution. -/
theorem exists_norm_riemannZeta_logDeriv_lowHeight_le
    {c H : ℝ} (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ smoothSaddleHTLowHeightCompact c H,
      z ≠ 1 →
      ‖deriv riemannZeta z / riemannZeta z‖ ≤ C + 1 / ‖z - 1‖ := by
  obtain ⟨C, hC, hsur⟩ :=
    exists_norm_logDeriv_sharpZetaSurrogate_lowHeight_le
      hc hH hZeroFree
  refine ⟨C, hC, ?_⟩
  intro z hz hzOne
  have hzeta : riemannZeta z ≠ 0 := by
    intro hzeta
    exact sharpZetaSurrogate_ne_zero_on_smoothSaddleHTLowHeightCompact
      hc hH hZeroFree hz
      ((GafniTao.sharpZetaSurrogate_eq_zero_iff hzOne).2 hzeta)
  have heq := GafniTao.logDeriv_sharpZetaSurrogate_eq hzOne hzeta
  have hsolve : logDeriv riemannZeta z =
      logDeriv GafniTao.sharpZetaSurrogate z - 1 / (z - 1) := by
    calc
      logDeriv riemannZeta z =
          (1 / (z - 1) + logDeriv riemannZeta z) - 1 / (z - 1) := by ring
      _ = logDeriv GafniTao.sharpZetaSurrogate z - 1 / (z - 1) := by
        rw [heq]
  rw [← logDeriv_apply, hsolve]
  calc
    ‖logDeriv GafniTao.sharpZetaSurrogate z - 1 / (z - 1)‖ ≤
        ‖logDeriv GafniTao.sharpZetaSurrogate z‖ + ‖1 / (z - 1)‖ :=
      norm_sub_le _ _
    _ ≤ C + 1 / ‖z - 1‖ := by
      exact add_le_add (hsur z hz) (by rw [norm_div, norm_one])

/-- Source-coordinate form on the low-height part of the shifted left edge.
The only singular cost is the expected reciprocal contour shift. -/
theorem exists_norm_riemannZeta_logDeriv_lowHeight_leftLine_le
    {c H : ℝ} (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {eta R : ℝ},
      0 < eta →
      eta ≤ c / (2 * GafniTao.vinogradovKorobovDenominator H) →
      |R| ≤ H →
      ‖deriv riemannZeta (((1 - eta : ℝ) : ℂ) + (R : ℂ) * Complex.I) /
          riemannZeta (((1 - eta : ℝ) : ℂ) + (R : ℂ) * Complex.I)‖ ≤
        C + 1 / eta := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_riemannZeta_logDeriv_lowHeight_le
      hc hH hZeroFree
  refine ⟨C, hC, ?_⟩
  intro eta R heta hetaWidth hR
  let z : ℂ := ((1 - eta : ℝ) : ℂ) + (R : ℂ) * Complex.I
  have hzRe : z.re = 1 - eta := by simp [z]
  have hzIm : z.im = R := by simp [z]
  have hzCompact : z ∈ smoothSaddleHTLowHeightCompact c H := by
    change z.re ∈ Set.Icc
        (1 - c / (2 * GafniTao.vinogradovKorobovDenominator H)) 2 ∧
      z.im ∈ Set.Icc (-H) H
    constructor
    · rw [hzRe]
      exact ⟨by linarith, by linarith⟩
    · rw [hzIm]
      exact (abs_le.mp hR)
  have hzOne : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
    linarith
  have hpole := hbound z hzCompact hzOne
  have hdist : eta ≤ ‖z - 1‖ := by
    have hre := Complex.abs_re_le_norm (z - 1)
    have hreEq : (z - 1).re = -eta := by simp [z]
    rw [hreEq, abs_neg, abs_of_pos heta] at hre
    exact hre
  have hnormPos : 0 < ‖z - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hzOne)
  have hinv : 1 / ‖z - 1‖ ≤ 1 / eta := by
    exact one_div_le_one_div_of_le heta hdist
  have hfinal : C + 1 / ‖z - 1‖ ≤ C + 1 / eta := by linarith
  simpa [z] using hpole.trans hfinal

end

end Tao2026
