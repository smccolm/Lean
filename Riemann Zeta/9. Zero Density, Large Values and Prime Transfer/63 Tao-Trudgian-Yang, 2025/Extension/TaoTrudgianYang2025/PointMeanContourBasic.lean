import TaoTrudgianYang2025.PointMeanGammaPole
import GuthMaynard.ZetaBounds

/-!
# Elementary bounds and orientations for the local-mean Mellin contour

Only the needed elementary statements from node 74's Pintz/Ford modules
are adapted: cubic Gamma decay, the actual Euler-series norm bound, and
the four oriented rectangle edges. No Ford or Pintz theorem is assumed.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped BigOperators Topology Interval ComplexOrder

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

theorem pintz2023_Gamma_positive_strip_decay
    {a t : ℝ} (haLower : 0 ≤ a) (haUpper : a ≤ 2) :
    |t| ^ 3 * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 := by
  by_cases ht : t = 0
  · subst t
    norm_num
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have hzFactor : ∀ j < (3 : ℕ), z + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have him := congrArg Complex.im hzero
    simp [z, ht] at him
  have hRec := Gamma_add_nat_eq_prod_mul z 3 hzFactor
  have hNormRec :
      ‖Complex.Gamma (z + 3)‖ =
        ‖∏ j ∈ Finset.range 3, (z + (j : ℂ))‖ * ‖Complex.Gamma z‖ := by
    have hRec' : Complex.Gamma (z + 3) =
        (∏ j ∈ Finset.range 3, (z + (j : ℂ))) * Complex.Gamma z := by
      simpa using hRec
    rw [hRec', norm_mul]
  have hProd : |t| ^ 3 ≤ ‖∏ j ∈ Finset.range 3, (z + (j : ℂ))‖ := by
    simpa [z] using abs_im_pow_le_norm_prod_horizontal a t 3
  have hShiftRe : (z + 3).re = a + 3 := by simp [z]
  have hShiftPos : 0 < (z + 3).re := by rw [hShiftRe]; linarith
  have hNormShift : ‖Complex.Gamma (z + 3)‖ ≤ Real.Gamma (a + 3) := by
    simpa [hShiftRe] using Complex.Gamma.norm_le_Gamma_re hShiftPos
  have hThree : (3 : ℝ) ≤ a + 3 := by linarith
  have hFive : a + 3 ≤ (5 : ℝ) := by linarith
  have hGammaMono : Real.Gamma (a + 3) ≤ Real.Gamma 5 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by linarith : (2 : ℝ) ≤ a + 3) (by norm_num) hFive
  have hGammaFive : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1
    norm_num
  have hShift : ‖Complex.Gamma (z + 3)‖ ≤ 24 :=
    hNormShift.trans (hGammaMono.trans_eq hGammaFive)
  rw [hNormRec] at hShift
  have hGap := mul_nonneg (sub_nonneg.mpr hProd)
    (norm_nonneg (Complex.Gamma z))
  nlinarith

theorem ford_norm_eq_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) :
    ‖z‖ = z.re := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  rw [Complex.norm_def, Complex.normSq_apply, ← him]
  rw [zero_mul, add_zero, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hre]

theorem ford_norm_riemannZeta_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hsumS : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  have hsumSigma : LSeriesSummable (1 : ℕ → ℂ) (sigma : ℂ) :=
    LSeriesSummable_one_iff.mpr hsigma
  rw [← LSeries_one_eq_riemannZeta hs,
    ← LSeries_one_eq_riemannZeta hsigma, LSeries, LSeries]
  calc
    ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤
        ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hsumS.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      apply hsumS.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re
          (1 : ℕ → ℂ) (by simp [s]) n)
        hsumSigma.norm
    _ = ‖∑' n, LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      have hnonneg (n : ℕ) :
          0 ≤ LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n :=
        LSeries.term_nonneg (by norm_num : (0 : ℂ) ≤ 1) sigma
      have hnormTerm (n : ℕ) :
          ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ =
            (LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n).re := by
        exact ford_norm_eq_re_of_nonneg (hnonneg n)
      simp_rw [hnormTerm]
      rw [← Complex.re_tsum hsumSigma]
      exact (ford_norm_eq_re_of_nonneg (tsum_nonneg hnonneg)).symm

theorem pintz2023_RectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

end TaoTrudgianYang2025
