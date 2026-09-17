import Tao2026.SmoothNumberSaddleHildebrandTenenbaumEnvelope
import Tao2026.QuantitativePNTBridge

/-!
# The Hildebrand--Tenenbaum Mangoldt transform

This module isolates the exact algebraic passage from HT Lemma 6 to its
cosine-sum corollary.  The weighted Mangoldt cosine loss is the real part of
the zero-frequency transform minus the transform at frequency `t`.  Hence
two uniform complex transform errors cost at most twice their common
majorant.  The remaining analytic task is to prove the transform estimate
from the native quantitative PNT/zero-free-region machinery.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The finite complex Mangoldt transform occurring in HT Lemma 6, written
with the real power and oscillatory exponential separated. -/
noncomputable def smoothSaddleHTMangoldtTransform
    (y : ℕ) (β t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (((Λ n : ℝ) * (n : ℝ) ^ (β - 1) : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The nonnegative weighted cosine sum extracted from the transform. -/
noncomputable def smoothSaddleHTMangoldtCosineSum
    (y : ℕ) (β t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 y,
    (Λ n : ℝ) * (n : ℝ) ^ (β - 1) *
      (1 - Real.cos (t * Real.log n))

/-- Exact real-part subtraction underlying the corollary to HT Lemma 6. -/
theorem smoothSaddleHTMangoldtCosineSum_eq_re_sub_transform
    (y : ℕ) (β t : ℝ) :
    smoothSaddleHTMangoldtCosineSum y β t =
      (smoothSaddleHTMangoldtTransform y β 0 -
        smoothSaddleHTMangoldtTransform y β t).re := by
  have hterm (A r : ℝ) :
      (Complex.ofReal A *
        Complex.exp (-(Complex.ofReal r) * Complex.I)).re =
          A * Real.cos r := by
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re]
  unfold smoothSaddleHTMangoldtCosineSum smoothSaddleHTMangoldtTransform
  rw [Complex.sub_re]
  change (∑ n ∈ Finset.Icc 1 y,
      (Λ n : ℝ) * (n : ℝ) ^ (β - 1) *
        (1 - Real.cos (t * Real.log n))) =
    Complex.reLm (∑ n ∈ Finset.Icc 1 y,
      (((Λ n : ℝ) * (n : ℝ) ^ (β - 1) : ℝ) : ℂ) *
        Complex.exp (-((0 * Real.log n : ℝ) : ℂ) * Complex.I)) -
    Complex.reLm (∑ n ∈ Finset.Icc 1 y,
      (((Λ n : ℝ) * (n : ℝ) ^ (β - 1) : ℝ) : ℂ) *
        Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I))
  rw [map_sum Complex.reLm, map_sum Complex.reLm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  change _ =
    (Complex.ofReal ((Λ n : ℝ) * (n : ℝ) ^ (β - 1)) *
      Complex.exp (-(Complex.ofReal (0 * Real.log n)) * Complex.I)).re -
    (Complex.ofReal ((Λ n : ℝ) * (n : ℝ) ^ (β - 1)) *
      Complex.exp (-(Complex.ofReal (t * Real.log n)) * Complex.I)).re
  rw [hterm, hterm]
  norm_num
  ring

/-- A source-shaped main term for the Mangoldt transform. -/
noncomputable def smoothSaddleHTMangoldtMainTerm
    (y : ℕ) (β t : ℝ) : ℂ :=
  (((y : ℝ) ^ β : ℝ) : ℂ) *
    Complex.exp (-((t * Real.log y : ℝ) : ℂ) * Complex.I) /
      ((β : ℂ) - (t : ℂ) * Complex.I)

/-- The corresponding exact real main term for the cosine sum. -/
noncomputable def smoothSaddleHTMangoldtCosineMainTerm
    (y : ℕ) (β t : ℝ) : ℝ :=
  (smoothSaddleHTMangoldtMainTerm y β 0 -
    smoothSaddleHTMangoldtMainTerm y β t).re

/-- Two complex transform approximations imply the cosine-sum approximation
with twice the common error. -/
theorem abs_smoothSaddleHTMangoldtCosineSum_sub_mainTerm_le
    {y : ℕ} {β t E : ℝ}
    (hzero : ‖smoothSaddleHTMangoldtTransform y β 0 -
      smoothSaddleHTMangoldtMainTerm y β 0‖ ≤ E)
    (hfreq : ‖smoothSaddleHTMangoldtTransform y β t -
      smoothSaddleHTMangoldtMainTerm y β t‖ ≤ E) :
    |smoothSaddleHTMangoldtCosineSum y β t -
      smoothSaddleHTMangoldtCosineMainTerm y β t| ≤ 2 * E := by
  rw [smoothSaddleHTMangoldtCosineSum_eq_re_sub_transform]
  unfold smoothSaddleHTMangoldtCosineMainTerm
  have hre : |((smoothSaddleHTMangoldtTransform y β 0 -
        smoothSaddleHTMangoldtTransform y β t) -
      (smoothSaddleHTMangoldtMainTerm y β 0 -
        smoothSaddleHTMangoldtMainTerm y β t)).re| ≤
      ‖(smoothSaddleHTMangoldtTransform y β 0 -
          smoothSaddleHTMangoldtTransform y β t) -
        (smoothSaddleHTMangoldtMainTerm y β 0 -
          smoothSaddleHTMangoldtMainTerm y β t)‖ :=
    Complex.abs_re_le_norm _
  calc
    |(smoothSaddleHTMangoldtTransform y β 0 -
          smoothSaddleHTMangoldtTransform y β t).re -
        (smoothSaddleHTMangoldtMainTerm y β 0 -
          smoothSaddleHTMangoldtMainTerm y β t).re| ≤
      ‖(smoothSaddleHTMangoldtTransform y β 0 -
          smoothSaddleHTMangoldtTransform y β t) -
        (smoothSaddleHTMangoldtMainTerm y β 0 -
          smoothSaddleHTMangoldtMainTerm y β t)‖ := by
        simpa only [Complex.sub_re] using hre
    _ = ‖(smoothSaddleHTMangoldtTransform y β 0 -
          smoothSaddleHTMangoldtMainTerm y β 0) -
        (smoothSaddleHTMangoldtTransform y β t -
          smoothSaddleHTMangoldtMainTerm y β t)‖ := by ring_nf
    _ ≤ ‖smoothSaddleHTMangoldtTransform y β 0 -
          smoothSaddleHTMangoldtMainTerm y β 0‖ +
        ‖smoothSaddleHTMangoldtTransform y β t -
          smoothSaddleHTMangoldtMainTerm y β t‖ := norm_sub_le _ _
    _ ≤ E + E := add_le_add hzero hfreq
    _ = 2 * E := by ring

end

end Tao2026
